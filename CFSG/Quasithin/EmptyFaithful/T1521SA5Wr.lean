module

public import CFSG.Quasithin.EmptyFaithful.T1521SA5Two
public import CFSG.Quasithin.EmptyFaithful.S153WJOff
public import CFSG.GroupTheory.QuasisimpleCommutingProductBound

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.A5S5
open scoped Pointwise commutatorElement

set_option synthInstance.maxSize 1000000
set_option synthInstance.maxHeartbeats 1000000

private theorem no_independent_triple : ∀ a : Equiv.Perm (Fin 5), a * a = 1 → a ≠ 1 →
    ∀ b : Equiv.Perm (Fin 5), b * b = 1 → b ≠ a → b ≠ 1 → a * b = b * a →
    ∀ c : Equiv.Perm (Fin 5), c * c = 1 → c ≠ 1 → c ≠ a → c ≠ b → c ≠ a * b →
      a * c = c * a → b * c = c * b → False := by
  decide +kernel

theorem card_le_four_of_elemAbelian_perm_five (E : Subgroup (Equiv.Perm (Fin 5)))
    (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hsq : ∀ x ∈ E, x * x = 1) :
    Nat.card E ≤ 4 := by
  classical
  by_contra hlt
  push Not at hlt
  have : Fintype E := Fintype.ofFinite E
  have hcard : 4 < Fintype.card E := by
    rw [Fintype.card_eq_nat_card]
    exact hlt
  obtain ⟨a, -, ha⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := ({1} : Finset E)) (t := Finset.univ)
    (by rw [Finset.card_singleton, Finset.card_univ]; omega)
  obtain ⟨b, -, hb⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := ({1, a} : Finset E)) (t := Finset.univ)
    (lt_of_le_of_lt Finset.card_le_two (by rw [Finset.card_univ]; omega))
  obtain ⟨c, -, hc⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := ({1, a, b, a * b} : Finset E)) (t := Finset.univ)
    (lt_of_le_of_lt Finset.card_le_four (by rw [Finset.card_univ]; omega))
  simp only [Finset.mem_singleton, Finset.mem_insert, not_or] at ha hb hc
  have hcom : ∀ x y : E, (x : Equiv.Perm (Fin 5)) * y = y * x := fun x y => hcomm x x.2 y y.2
  refine no_independent_triple a (hsq a a.2) (fun h => ha (Subtype.ext h)) b (hsq b b.2)
    (fun h => hb.2 (Subtype.ext h)) (fun h => hb.1 (Subtype.ext h)) (hcom a b) c (hsq c c.2)
    (fun h => hc.1 (Subtype.ext h)) (fun h => hc.2.1 (Subtype.ext h))
    (fun h => hc.2.2.1 (Subtype.ext h)) (fun h => hc.2.2.2 (Subtype.ext h)) (hcom a c) (hcom b c)

private theorem alt_pow_four_aux :
    ∀ k : Equiv.Perm (Fin 5), Equiv.Perm.sign k = 1 → k ^ 4 = 1 → k ^ 2 = 1 := by
  decide +kernel

variable {G : Type} [Group G]

private theorem conjByElt_mul_aux (s t : G) (K : Subgroup G) :
    conjByElt (s * t) K = conjByElt s (conjByElt t K) := by
  ext x
  rw [mem_conjByElt, mem_conjByElt, mem_conjByElt]
  rw [mul_inv_rev]
  group

private theorem conjByElt_one_aux (K : Subgroup G) : conjByElt 1 K = K := by
  ext x
  rw [mem_conjByElt]
  simp

private theorem mem_normalizer_of_conjByElt_eq_aux {y : G} {L : Subgroup G}
    (h : conjByElt y L = L) : y ∈ Subgroup.normalizer (L : Set G) :=
  Subgroup.mem_normalizer_iff_map_conj_eq.mpr h

private theorem isElemAbelian_conjByElt_aux {V : Subgroup G} (hV : IsElemAbelian 2 V) (a : G) :
    IsElemAbelian 2 (conjByElt a V) := by
  refine ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩
  · obtain ⟨x, u, hu, rfl⟩ := x
    obtain ⟨y, v, hv, rfl⟩ := y
    apply Subtype.ext
    have h := congrArg Subtype.val (hV.1.is_comm.comm (⟨u, hu⟩ : V) ⟨v, hv⟩)
    change (a * u * a⁻¹) * (a * v * a⁻¹) = (a * v * a⁻¹) * (a * u * a⁻¹)
    have h' : u * v = v * u := h
    calc (a * u * a⁻¹) * (a * v * a⁻¹) = a * (u * v) * a⁻¹ := by group
      _ = a * (v * u) * a⁻¹ := by rw [h']
      _ = (a * v * a⁻¹) * (a * u * a⁻¹) := by group
  · obtain ⟨u, hu, rfl⟩ := hx
    have h := hV.2 u hu
    change (a * u * a⁻¹) ^ 2 = 1
    rw [conj_pow, h]
    group

private theorem imageUnder_elemAbelian {N : Subgroup G} {π : N →* Equiv.Perm (Fin 5)}
    {A : Subgroup G} (hA : IsElemAbelian 2 A) :
    (∀ g ∈ imageUnder π A, g * g = 1) ∧
      ∀ g ∈ imageUnder π A, ∀ h ∈ imageUnder π A, g * h = h * g := by
  constructor
  · intro g hg
    obtain ⟨y, hy, rfl⟩ := mem_imageUnder.1 hg
    have : y * y = 1 := Subtype.ext (by simpa [pow_two] using hA.2 _ hy)
    rw [← map_mul, this, map_one]
  · intro g hg h hh
    obtain ⟨y, hy, rfl⟩ := mem_imageUnder.1 hg
    obtain ⟨z, hz, rfl⟩ := mem_imageUnder.1 hh
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (B2F.isElemAbelian_comm hA hy hz)

private theorem card_imageUnder_mul_card_inf {N : Subgroup G} {π : N →* Equiv.Perm (Fin 5)}
    {C A : Subgroup G} (hAN : A ≤ N) (hC : ∀ y : N, π y = 1 ↔ (y : G) ∈ C) :
    Nat.card (imageUnder π A) * Nat.card ↥(A ⊓ C) = Nat.card A := by
  set K' := A.subgroupOf N with hK'
  have h1 := Subgroup.card_ker_mul_card_range (π.domRestrict K')
  rw [MonoidHom.domRestrict_range] at h1
  have h2 : Nat.card K' = Nat.card A := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAN).toEquiv
  have h3 : Nat.card (π.domRestrict K').ker = Nat.card ↥(A ⊓ C) := by
    refine Nat.card_congr
      { toFun := fun y => ⟨(y.1.1 : G), y.1.2, (hC y.1.1).1 y.2⟩
        invFun := fun k => ⟨⟨⟨k, hAN k.2.1⟩, Subgroup.mem_subgroupOf.2 k.2.1⟩, (hC _).2 k.2.2⟩
        left_inv := fun y => rfl
        right_inv := fun k => rfl }
  rw [← h2, ← h1, h3]
  show Nat.card (Subgroup.map π K') * _ = _
  ring

private theorem eq_one_of_central_alt5 {L : Subgroup G} (e : ↥L ≃* alternatingGroup (Fin 5))
    {z : G} (hz : z ∈ L) (hc : ∀ y ∈ L, y * z = z * y) : z = 1 := by
  have h1 : (⟨z, hz⟩ : ↥L) ∈ Subgroup.center ↥L := by
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (hc y.1 y.2)
  have h2 : e ⟨z, hz⟩ ∈ Subgroup.center (alternatingGroup (Fin 5)) := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨y, rfl⟩ := e.surjective g
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subgroup.mem_center_iff.mp h1 y
  rw [alternatingGroup.center_eq_bot (by simp), Subgroup.mem_bot] at h2
  have h3 : (⟨z, hz⟩ : ↥L) = 1 := e.injective (h2.trans (map_one e).symm)
  exact congrArg Subtype.val h3

variable [Finite G]

theorem le_normalizer_of_wreath_two {S L : Subgroup G} (hL : IsPSL 2 2 2 ↥L)
    (hSyl : IsSylowTwoOf (S ⊓ L) L) {t : G} (hset : conjSubgroupsBy S L = {L, conjByElt t L})
    (hcomm : ⁅L, conjByElt t L⁆ = ⊥) {A : Subgroup G} (hA : IsMaxElemAbelian S A) :
    A ≤ Subgroup.normalizer (L : Set G) := by
  classical
  by_contra hAnot
  obtain ⟨a, haA, han⟩ : ∃ a ∈ A, a ∉ Subgroup.normalizer (L : Set G) := by
    by_contra h
    exact hAnot fun x hx => by
      by_contra hc
      exact h ⟨x, hx, hc⟩
  have haS : a ∈ S := hA.1 haA
  have hM : ∀ y ∈ S, y ∉ Subgroup.normalizer (L : Set G) → conjByElt y L = conjByElt t L := by
    intro y hy hyn
    have h1 : conjByElt y L ∈ conjSubgroupsBy S L := ⟨y, hy, rfl⟩
    rw [hset] at h1
    rcases h1 with h1 | h1
    · exact absurd (mem_normalizer_of_conjByElt_eq_aux h1) hyn
    · exact h1
  have hMa : conjByElt a L = conjByElt t L := hM a haS han
  have hAcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hA.2.1.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have ha2 : a * a = 1 := by
    have := hA.2.1.2 a haA
    rwa [sq] at this
  have hhalf : ∀ x ∈ A, x ∈ A ⊓ Subgroup.normalizer (L : Set G) ∨
      a⁻¹ * x ∈ A ⊓ Subgroup.normalizer (L : Set G) := by
    intro x hx
    by_cases hxn : x ∈ Subgroup.normalizer (L : Set G)
    · exact Or.inl ⟨hx, hxn⟩
    · right
      refine ⟨A.mul_mem (A.inv_mem haA) hx, ?_⟩
      have h1 : conjByElt x L = conjByElt a L := (hM x (hA.1 hx) hxn).trans hMa.symm
      apply mem_normalizer_of_conjByElt_eq_aux
      rw [conjByElt_mul_aux, h1, ← conjByElt_mul_aux, inv_mul_cancel, conjByElt_one_aux]
  have hindexA : Nat.card A ≤ 2 * Nat.card ↥(A ⊓ Subgroup.normalizer (L : Set G)) :=
    W153.card_le_two_mul_of_forall inf_le_left hAcomm haA ha2 hhalf
  obtain ⟨e⟩ := nonempty_equiv_alt5_of_isPSL_two_two_two hL
  set ρ := CFSG.OddStandard.rhoOf e with hρ
  have hπe : ∀ (ℓ : G) (hℓ : ℓ ∈ L), ρ ⟨ℓ, Subgroup.le_normalizer hℓ⟩ =
      ((e ⟨ℓ, hℓ⟩ : alternatingGroup (Fin 5)) : Equiv.Perm (Fin 5)) := fun ℓ hℓ =>
    CFSG.OddStandard.rhoOf_apply_of_mem e hℓ
  have hkerC : ∀ y : ↥(Subgroup.normalizer (L : Set G)), ρ y = 1 ↔
      (y : G) ∈ Subgroup.centralizer (L : Set G) := by
    intro y
    rw [← MonoidHom.mem_ker, hρ, CFSG.OddStandard.rhoOf_ker e, Subgroup.mem_subgroupOf]
  have hZ : ∀ z ∈ L, (∀ y ∈ L, y * z = z * y) → z = 1 := fun z hz hc =>
    eq_one_of_central_alt5 e hz hc
  set C : Subgroup G := A ⊓ Subgroup.centralizer (L : Set G) with hCdef
  have hA0C : (A ⊓ Subgroup.normalizer (L : Set G)) ⊓ Subgroup.centralizer (L : Set G) = C := by
    ext x
    constructor
    · exact fun hx => ⟨hx.1.1, hx.2⟩
    · exact fun hx => ⟨⟨hx.1, Subgroup.centralizer_le_normalizer _ hx.2⟩, hx.2⟩
  have hcardA0 := card_imageUnder_mul_card_inf (π := ρ) (A := A ⊓ Subgroup.normalizer (L : Set G))
    (C := Subgroup.centralizer (L : Set G)) inf_le_right hkerC
  rw [hA0C] at hcardA0
  have hA0ea : IsElemAbelian 2 (A ⊓ Subgroup.normalizer (L : Set G)) :=
    B2F.isElemAbelian_mono inf_le_left hA.2.1
  have hea := imageUnder_elemAbelian (π := ρ) hA0ea
  have h4 : Nat.card (imageUnder ρ (A ⊓ Subgroup.normalizer (L : Set G))) ≤ 4 :=
    card_le_four_of_elemAbelian_perm_five _ hea.2 hea.1
  have hAC : Nat.card A ≤ 8 * Nat.card C := by
    calc Nat.card A ≤ 2 * Nat.card ↥(A ⊓ Subgroup.normalizer (L : Set G)) := hindexA
      _ = 2 * (Nat.card (imageUnder ρ (A ⊓ Subgroup.normalizer (L : Set G))) * Nat.card C) := by
        rw [hcardA0]
      _ ≤ 2 * (4 * Nat.card C) := by gcongr
      _ = 8 * Nat.card C := by ring
  set VL : Subgroup G := S ⊓ L with hVLdef
  have hVLL : VL ≤ L := inf_le_right
  have hπe' : ∀ (ℓ : G) (hℓ : ℓ ∈ L), ρ ⟨ℓ, Subgroup.le_normalizer hℓ⟩ =
      ((e.toMonoidHom ⟨ℓ, hℓ⟩ : alternatingGroup (Fin 5)) : Equiv.Perm (Fin 5)) := hπe
  have hKalt : imageUnder ρ VL ≤ alternatingGroup (Fin 5) :=
    imageUnder_le_alt Subgroup.le_normalizer e.toMonoidHom hπe' hVLL
  have hKcard : Nat.card (imageUnder ρ VL) = 4 :=
    card_imageUnder_eq_four Subgroup.le_normalizer e.toMonoidHom hπe' e.surjective hVLL
      (by rw [(MonoidHom.ker_eq_bot_iff _).2 e.injective]; exact bot_le) hSyl.2.1 hSyl.2.2
  have hinj : Function.Injective ((alternatingGroup (Fin 5)).subtype.comp e.toMonoidHom) :=
    fun x y h => e.injective (Subtype.ext h)
  have hVL4 : Nat.card VL = 4 := by
    rw [← hKcard, imageUnder_eq_map Subgroup.le_normalizer e.toMonoidHom hπe' hVLL,
      Subgroup.card_map_of_injective hinj]
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVLL).toEquiv).symm
  have hVLsq : ∀ x ∈ VL, x * x = 1 := by
    intro x hx
    have hxL : x ∈ L := hVLL hx
    have hmem : ρ ⟨x, Subgroup.le_normalizer hxL⟩ ∈ imageUnder ρ VL :=
      pi_mem_imageUnder (π := ρ) (y := ⟨x, Subgroup.le_normalizer hxL⟩) hx
    have h4' : (⟨ρ ⟨x, Subgroup.le_normalizer hxL⟩, hmem⟩ : imageUnder ρ VL) ^ 4 = 1 := by
      have := pow_card_eq_one' (G := imageUnder ρ VL)
        (x := ⟨ρ ⟨x, Subgroup.le_normalizer hxL⟩, hmem⟩)
      rwa [hKcard] at this
    have h4'' : (ρ ⟨x, Subgroup.le_normalizer hxL⟩) ^ 4 = 1 := by
      have := congrArg Subtype.val h4'
      simpa using this
    have hsgn : Equiv.Perm.sign (ρ ⟨x, Subgroup.le_normalizer hxL⟩) = 1 :=
      Equiv.Perm.mem_alternatingGroup.mp (hKalt hmem)
    have h2 := alt_pow_four_aux _ hsgn h4''
    have hxx : ρ ⟨x * x, Subgroup.le_normalizer (L.mul_mem hxL hxL)⟩ = 1 := by
      have : (⟨x * x, Subgroup.le_normalizer (L.mul_mem hxL hxL)⟩ :
          ↥(Subgroup.normalizer (L : Set G))) = ⟨x, Subgroup.le_normalizer hxL⟩ ^ 2 := by
        apply Subtype.ext; simp [pow_two]
      rw [this, map_pow]
      exact h2
    have hxxC := (hkerC _).1 hxx
    exact hZ (x * x) (L.mul_mem hxL hxL) (fun y hy => (Subgroup.mem_centralizer_iff.mp hxxC y hy))
  have hVLcomm : ∀ x ∈ VL, ∀ y ∈ VL, x * y = y * x := by
    intro x hx y hy
    have hxy := hVLsq (x * y) (VL.mul_mem hx hy)
    have hx' := hVLsq x hx
    have hy' := hVLsq y hy
    calc x * y = (x * y)⁻¹ := (inv_eq_of_mul_eq_one_right hxy).symm
      _ = y⁻¹ * x⁻¹ := mul_inv_rev _ _
      _ = y * x := by rw [inv_eq_of_mul_eq_one_right hy', inv_eq_of_mul_eq_one_right hx']
  have hVLea : IsElemAbelian 2 VL :=
    ⟨⟨⟨fun x y => Subtype.ext (hVLcomm x x.2 y y.2)⟩⟩, fun x hx => by
      simpa [sq] using hVLsq x hx⟩
  set VM : Subgroup G := conjByElt a VL with hVMdef
  have hVMS : VM ≤ S := by
    rintro _ ⟨y, hy, rfl⟩
    exact S.mul_mem (S.mul_mem haS hy.1) (S.inv_mem haS)
  have hVMM : VM ≤ conjByElt t L := by
    rw [← hMa]
    exact Subgroup.map_mono hVLL
  have hLM : ∀ x ∈ L, ∀ y ∈ conjByElt t L, x * y = y * x := by
    intro x hx y hy
    have hle := Subgroup.commutator_eq_bot_iff_le_centralizer.1 hcomm
    exact (Subgroup.mem_centralizer_iff.1 (hle hx) y hy).symm
  have hcommLM : ∀ x ∈ VL, ∀ y ∈ VM, x * y = y * x := fun x hx y hy =>
    hLM x (hVLL hx) y (hVMM hy)
  have hVMea : IsElemAbelian 2 VM := isElemAbelian_conjByElt_aux hVLea a
  have hUea : IsElemAbelian 2 (VL ⊔ VM) := B2F.isElemAbelian_sup_of_commute hVLea hVMea hcommLM
  have hbot : VL ⊓ VM = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have hzL : z ∈ L := hVLL hz.1
    have hzM : z ∈ conjByElt t L := hVMM hz.2
    have hz1 : z = 1 := hZ z hzL (fun y hy => hLM y hy z hzM)
    rw [hz1]
    exact Subgroup.one_mem _
  have hVMcard : Nat.card VM = Nat.card VL :=
    Subgroup.card_map_of_injective (f := (MulAut.conj a).toMonoidHom) (MulAut.conj a).injective
  have hUcard : Nat.card ↥(VL ⊔ VM) = 16 := by
    have h := B2F.card_sup_mul_card_inf_of_commute hcommLM
    rw [hbot, Subgroup.card_bot, mul_one, hVMcard, hVL4] at h
    omega
  have hCea : IsElemAbelian 2 C := B2F.isElemAbelian_mono inf_le_left hA.2.1
  have hCcomm : ∀ c ∈ C, ∀ u ∈ VL ⊔ VM, c * u = u * c := by
    intro c hc u hu
    have hcVL : ∀ h ∈ VL, h * c = c * h := fun h hh =>
      Subgroup.mem_centralizer_iff.mp hc.2 h (hVLL hh)
    have hac : Commute a c := hAcomm a haA c hc.1
    have hcVM : ∀ h ∈ VM, h * c = c * h := by
      rintro _ ⟨v, hv, rfl⟩
      have hvc : Commute v c := hcVL v hv
      exact (((hac.mul_left hvc).mul_left hac.inv_left) : Commute (a * v * a⁻¹) c).eq
    have hle : VL ⊔ VM ≤ Subgroup.centralizer ({c} : Set G) := by
      refine sup_le (fun h hh => ?_) (fun h hh => ?_)
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact hcVL h hh
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact hcVM h hh
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hle hu)).symm
  have hWea : IsElemAbelian 2 (VL ⊔ VM ⊔ C) :=
    B2F.isElemAbelian_sup_of_commute hUea hCea (fun u hu c hc => (hCcomm c hc u hu).symm)
  have hWS : VL ⊔ VM ⊔ C ≤ S := sup_le (sup_le inf_le_left hVMS) (inf_le_left.trans hA.1)
  have hWA : Nat.card ↥(VL ⊔ VM ⊔ C) ≤ Nat.card A := hA.2.2 _ hWS hWea
  have hUC : (VL ⊔ VM) ⊓ C = ⊥ := by
    rw [eq_bot_iff]
    rintro z ⟨hzU, hzC⟩
    have hset' := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute VL VM hcommLM).2
    have hzmem : z ∈ (VL : Set G) * (VM : Set G) := by rw [← hset']; exact hzU
    obtain ⟨v, hv, w, hw, rfl⟩ := hzmem
    have hv1 : v = 1 := by
      refine hZ v (hVLL hv) fun y hy => ?_
      have h1 := Subgroup.mem_centralizer_iff.mp hzC.2 y hy
      have h2 : y * w = w * y := hLM y hy w (hVMM hw)
      have h3 : y * v * w = v * y * w := by
        calc y * v * w = y * (v * w) := by group
          _ = (v * w) * y := h1
          _ = v * (w * y) := by group
          _ = v * (y * w) := by rw [h2]
          _ = v * y * w := by group
      exact mul_right_cancel h3
    subst hv1
    have hw0 := hw
    obtain ⟨x, hx, hxw⟩ := hw
    have hxw' : a * x * a⁻¹ = w := hxw
    have hcw : a * w = w * a := by
      have := hAcomm a haA (1 * w) hzC.1
      simpa using this
    have hconj : a * w * a⁻¹ = w := mul_inv_eq_iff_eq_mul.mpr hcw
    have hwx : w = x := by
      calc w = a * w * a⁻¹ := hconj.symm
        _ = a * (a * x * a⁻¹) * a⁻¹ := by rw [hxw']
        _ = (a * a) * x * (a * a)⁻¹ := by group
        _ = x := by rw [ha2]; group
    have hwbot : w ∈ VL ⊓ VM := ⟨by rw [hwx]; exact hx, hw0⟩
    rw [hbot, Subgroup.mem_bot] at hwbot
    rw [hwbot]
    simp
  have hcardW := B2F.card_sup_mul_card_inf_of_commute (A := VL ⊔ VM) (B := C)
    (fun u hu c hc => (hCcomm c hc u hu).symm)
  rw [hUC, Subgroup.card_bot, mul_one, hUcard] at hcardW
  have hCpos : 0 < Nat.card C := Nat.card_pos
  omega

end CFSG.Quasithin
