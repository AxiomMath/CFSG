module

public import CFSG.Quasithin.EmptyFaithful.S151YG
public import CFSG.CharacterTheory.Burnside

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {G : Type} [Group G]

theorem ya7_gamma {L : Subgroup G} {α : ↥L →* alternatingGroup (Fin 7)}
    (hα : IsAltBlockTypeWith L 7 α) :
    ∃ γ : ↥(blockU L) →* Multiplicative ↥(evenWeight 7), Function.Surjective γ ∧
      ∀ (ℓ : ↥L) (u v : ↥(blockU L)), (v : G) = ℓ * u * ℓ⁻¹ →
        Multiplicative.toAdd (γ v) =
          permWeight 7 (α ℓ : Equiv.Perm (Fin 7)) (Multiplicative.toAdd (γ u)) := by
  obtain ⟨-, -, β, hβs, -, hβeq⟩ := hα
  have hq := altHeart_mk_bijective (m := 7) (by decide)
  let q : ↥(evenWeight 7) →+ AltHeart 7 := QuotientAddGroup.mk' (constWeight 7)
  let e : ↥(evenWeight 7) ≃+ AltHeart 7 := AddEquiv.ofBijective q hq
  refine ⟨(AddMonoidHom.toMultiplicative e.symm.toAddMonoidHom).comp β, ?_, ?_⟩
  · intro y
    obtain ⟨a, ha⟩ := e.symm.surjective (Multiplicative.toAdd y)
    obtain ⟨u, hu⟩ := hβs (Multiplicative.ofAdd a)
    refine ⟨u, ?_⟩
    apply Multiplicative.toAdd.injective
    show e.symm (Multiplicative.toAdd (β u)) = Multiplicative.toAdd y
    rw [hu]
    exact ha
  · intro ℓ u v huv
    set y : ↥(evenWeight 7) := e.symm (Multiplicative.toAdd (β u)) with hy
    have hyq : (QuotientAddGroup.mk y : AltHeart 7) = Multiplicative.toAdd (β u) := by
      have := e.apply_symm_apply (Multiplicative.toAdd (β u))
      exact this
    have h1 := hβeq ℓ u v huv y hyq
    have h2 : e.symm (Multiplicative.toAdd (β v)) =
        permWeight 7 (α ℓ : Equiv.Perm (Fin 7)) y := by
      rw [← h1]
      exact e.symm_apply_apply _
    show e.symm (Multiplicative.toAdd (β v)) =
      permWeight 7 (α ℓ : Equiv.Perm (Fin 7)) (e.symm (Multiplicative.toAdd (β u)))
    rw [h2]

theorem ya7_perm_eq_one (σ : Equiv.Perm (Fin 7))
    (h : ∀ z : ↥(evenWeight 7), permWeight 7 σ z = z) : σ = 1 := by
  have hsum : ∀ a b : Fin 7, a ≠ b →
      ∑ i : Fin 7, (if i = a ∨ i = b then (1 : ZMod 2) else 0) = 0 := by decide
  have hne : ∀ a : Fin 7, a ≠ a + 1 ∧ a ≠ a + 2 ∧ a + 1 ≠ a + 2 := by decide
  have hvec : ∀ a b : Fin 7, a ≠ b → ∃ z : ↥(evenWeight 7),
      ∀ i, (z : Fin 7 → ZMod 2) i = if i = a ∨ i = b then 1 else 0 := by
    intro a b hab
    refine ⟨⟨fun i => if i = a ∨ i = b then 1 else 0, ?_⟩, fun i => rfl⟩
    simp only [evenWeight, AddMonoidHom.mem_ker, AddMonoidHom.mk'_apply]
    exact hsum a b hab
  refine Equiv.ext fun a => ?_
  obtain ⟨z, hz⟩ := hvec a (a + 1) (hne a).1
  obtain ⟨z', hz'⟩ := hvec a (a + 2) (hne a).2.1
  have h1 := congrArg (fun w : ↥(evenWeight 7) => (w : Fin 7 → ZMod 2) a) (h z)
  have h2 := congrArg (fun w : ↥(evenWeight 7) => (w : Fin 7 → ZMod 2) a) (h z')
  simp only [permWeight, hz, hz'] at h1 h2
  have h1' : σ⁻¹ a = a ∨ σ⁻¹ a = a + 1 := by
    by_contra hcon
    simp only [hcon, ite_false, true_or, ite_true] at h1
    exact absurd h1 (by decide)
  have h2' : σ⁻¹ a = a ∨ σ⁻¹ a = a + 2 := by
    by_contra hcon
    simp only [hcon, ite_false, true_or, ite_true] at h2
    exact absurd h2 (by decide)
  have h3 : σ⁻¹ a = a := by
    rcases h1' with h | h
    · exact h
    · rcases h2' with h' | h'
      · exact h'
      · exact absurd (h.symm.trans h') (hne a).2.2
  have h4 : a = σ a := Equiv.Perm.inv_eq_iff_eq.mp h3
  exact h4.symm

theorem ya7_blockU_le [Finite G] (L : Subgroup G) : blockU L ≤ pCoreOf 2 L := by
  unfold blockU blockQ
  refine Subgroup.commutator_le.2 fun r hr ℓ hℓ => ?_
  have h := (Subgroup.mem_normalizer_iff.1
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L hℓ) r⁻¹).1 ((pCoreOf 2 L).inv_mem hr)
  have e : ⁅r, ℓ⁆ = r * (ℓ * r⁻¹ * ℓ⁻¹) := by rw [commutatorElement_def]; group
  rw [e]
  exact (pCoreOf 2 L).mul_mem hr h

theorem ya7_centralizer_le [Finite G] {L : Subgroup G} {α : ↥L →* alternatingGroup (Fin 7)}
    (hα : IsAltBlockTypeWith L 7 α) :
    L ⊓ Subgroup.centralizer (pCoreOf 2 L : Set G) ≤ pCoreOf 2 L := by
  obtain ⟨γ, hγs, hγe⟩ := ya7_gamma hα
  have hker : α.ker = CFSG.Open.pCore 2 ↥L := by rw [hα.2.1]
  rintro c ⟨hcL, hcC⟩
  have hfix : ∀ z : ↥(evenWeight 7),
      permWeight 7 (α ⟨c, hcL⟩ : Equiv.Perm (Fin 7)) z = z := by
    intro z
    obtain ⟨u, hu⟩ := hγs (Multiplicative.ofAdd z)
    have hu' : Multiplicative.toAdd (γ u) = z := by rw [hu]; rfl
    have hcom : (u : G) * c = c * (u : G) :=
      Subgroup.mem_centralizer_iff.mp hcC (u : G) (ya7_blockU_le L u.2)
    have hcu : (u : G) = ((⟨c, hcL⟩ : ↥L) : G) * (u : G) * ((⟨c, hcL⟩ : ↥L) : G)⁻¹ := by
      show (u : G) = c * (u : G) * c⁻¹
      rw [← hcom]
      group
    have := hγe ⟨c, hcL⟩ u u hcu
    rw [hu'] at this
    exact this.symm
  have hσ := ya7_perm_eq_one _ hfix
  have hα1 : α ⟨c, hcL⟩ = 1 := Subtype.ext hσ
  exact (mem_pCoreOf_iff_ker hker).mpr ⟨hcL, hα1⟩

theorem ya7_centralizer_normalizer {R : Subgroup G} {h : G}
    (hh : h ∈ Subgroup.normalizer (R : Set G)) :
    h ∈ Subgroup.normalizer ((Subgroup.centralizer (R : Set G) : Subgroup G) : Set G) := by
  have key : ∀ g ∈ Subgroup.normalizer (R : Set G), ∀ c ∈ Subgroup.centralizer (R : Set G),
      g * c * g⁻¹ ∈ Subgroup.centralizer (R : Set G) := by
    intro g hg c hc
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    have hr' : g⁻¹ * r * g ∈ R := by
      have := (Subgroup.mem_normalizer_iff.mp (inv_mem hg) r).mp hr
      simpa using this
    have hcomm : (g⁻¹ * r * g) * c = c * (g⁻¹ * r * g) := Subgroup.mem_centralizer_iff.mp hc _ hr'
    calc r * (g * c * g⁻¹) = g * ((g⁻¹ * r * g) * c) * g⁻¹ := by group
      _ = g * (c * (g⁻¹ * r * g)) * g⁻¹ := by rw [hcomm]
      _ = (g * c * g⁻¹) * r := by group
  rw [Subgroup.mem_normalizer_iff]
  intro c
  constructor
  · exact key h hh c
  · intro hc
    have := key h⁻¹ (inv_mem hh) _ hc
    simpa [mul_assoc] using this

variable {L S : Subgroup G} {α : ↥L →* alternatingGroup (Fin 7)} {P : Finset (Finset (Fin 7))}

theorem Ya7Core.charTwo [Finite G] (hc : Ya7Core L S α P)
    (hCL : L ⊓ Subgroup.centralizer (pCoreOf 2 L : Set G) ≤ pCoreOf 2 L) :
    CharTwo (ya7Pre L α P ⊔ S) := by
  have hRp : IsPGroup 2 ↥(pCoreOf 2 L) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L
  have hHL : ya7Pre L α P ⊔ S ≤ Subgroup.normalizer (L : Set G) :=
    sup_le ((ya7Pre_le L α P).trans Subgroup.le_normalizer) hc.norm
  have hHR : ya7Pre L α P ⊔ S ≤ Subgroup.normalizer (pCoreOf 2 L : Set G) :=
    hHL.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L)
  have hRH : pCoreOf 2 L ≤ ya7Pre L α P ⊔ S := hc.pCoreOf_le_pre.trans le_sup_left
  have hRO : pCoreOf 2 L ≤ pCoreOf 2 (ya7Pre L α P ⊔ S) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hRH hHR hRp
  set X := (ya7Pre L α P ⊔ S) ⊓ Subgroup.centralizer (pCoreOf 2 L : Set G) with hX
  have hXH : X ≤ ya7Pre L α P ⊔ S := inf_le_left
  have hHX : ya7Pre L α P ⊔ S ≤ Subgroup.normalizer (X : Set G) := fun h hh =>
    Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer hh, ya7_centralizer_normalizer (hHR hh)⟩
  have hXp : IsPGroup 2 ↥X := by
    intro x
    obtain ⟨k, hk⟩ := hc.two_pow (x : G) (hXH x.2)
    have h1 : (x : G) ^ 2 ^ k ∈ Subgroup.centralizer (pCoreOf 2 L : Set G) :=
      Subgroup.pow_mem _ x.2.2 _
    have h2 : (x : G) ^ 2 ^ k ∈ pCoreOf 2 L := hCL ⟨ya7Pre_le L α P hk, h1⟩
    obtain ⟨m, hm⟩ := hRp ⟨(x : G) ^ 2 ^ k, h2⟩
    refine ⟨k + m, ?_⟩
    apply Subtype.ext
    have := congrArg Subtype.val hm
    simp only [Subgroup.coe_pow, Subgroup.coe_one] at this ⊢
    rw [pow_add, pow_mul]
    exact this
  have hXO : X ≤ pCoreOf 2 (ya7Pre L α P ⊔ S) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hXH hHX hXp
  intro x ⟨hxH, hxC⟩
  exact hXO ⟨hxH, Subgroup.centralizer_le hRO hxC⟩

theorem ya7_isSolvable_of_card {Y : Type*} [Group Y] [Finite Y] {n : ℕ}
    (h : Nat.card Y = 2 ^ n * 3) : Group.IsSolvable Y := by
  let _ : Fintype Y := Fintype.ofFinite Y
  exact CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow (a := n) (b := 1)
    Nat.prime_two Nat.prime_three (by norm_num) (by rw [← Nat.card_eq_fintype_card, h, pow_one])

theorem Ya7Core.isSolvable_pre [Finite G] (hc : Ya7Core L S α P) :
    Group.IsSolvable ↥(ya7Pre L α P) := by
  obtain ⟨-, hcard, -⟩ := ya7_data (ya7D L S α) hc.sylowD hc.part hc.stabD
  have hRp : IsPGroup 2 ↥(pCoreOf 2 L) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L
  have hnil : Group.IsNilpotent ↥(pCoreOf 2 L) := hRp.isNilpotent
  have : Group.IsSolvable ↥(pCoreOf 2 L) := inferInstance
  have : Group.IsSolvable ↥(ya7PartStab P) :=
    ya7_isSolvable_of_card (n := 3) (by rw [hcard]; norm_num)
  let f : ↥(pCoreOf 2 L) →* ↥(ya7Pre L α P) := Subgroup.inclusion hc.pCoreOf_le_pre
  let g : ↥(ya7Pre L α P) →* ↥(ya7PartStab P) :=
    (α.comp (Subgroup.inclusion (ya7Pre_le L α P))).codRestrict (ya7PartStab P)
      (fun x => (mem_ya7Pre.mp x.2).2)
  refine Group.isSolvable_of_ker_le_range f g fun x hx => ?_
  have h1 : α (Subgroup.inclusion (ya7Pre_le L α P) x) = 1 := by
    have := congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
    exact this
  have hxR : (x : G) ∈ pCoreOf 2 L :=
    (mem_pCoreOf_iff_ker hc.ker).mpr ⟨ya7Pre_le L α P x.2, h1⟩
  exact ⟨⟨x, hxR⟩, rfl⟩

theorem Ya7Core.isSolvable_H [Finite G] (hc : Ya7Core L S α P) :
    Group.IsSolvable ↥(ya7Pre L α P ⊔ S) := by
  have := hc.isSolvable_pre
  have hn : ((ya7Pre L α P).subgroupOf (ya7Pre L α P ⊔ S)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr hc.H_le_normalizer
  have hq : IsPGroup 2 (↥(ya7Pre L α P ⊔ S) ⧸ (ya7Pre L α P).subgroupOf (ya7Pre L α P ⊔ S)) := by
    intro g
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective g
    obtain ⟨k, hk⟩ := hc.two_pow (x : G) x.2
    refine ⟨k, ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact Subgroup.mem_subgroupOf.mpr (by simpa using hk)
  have hnil : Group.IsNilpotent
      (↥(ya7Pre L α P ⊔ S) ⧸ (ya7Pre L α P).subgroupOf (ya7Pre L α P ⊔ S)) := hq.isNilpotent
  have : Group.IsSolvable
      (↥(ya7Pre L α P ⊔ S) ⧸ (ya7Pre L α P).subgroupOf (ya7Pre L α P ⊔ S)) := inferInstance
  refine Group.isSolvable_of_ker_le_range (Subgroup.inclusion (le_sup_left : ya7Pre L α P ≤ ya7Pre L α P ⊔ S))
    (QuotientGroup.mk' ((ya7Pre L α P).subgroupOf (ya7Pre L α P ⊔ S))) fun x hx => ?_
  rw [QuotientGroup.ker_mk'] at hx
  exact ⟨⟨x, Subgroup.mem_subgroupOf.mp hx⟩, rfl⟩

end CFSG.Quasithin
