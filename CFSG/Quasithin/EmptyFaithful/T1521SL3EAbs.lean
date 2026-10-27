module

public import CFSG.LocalAnalysis.SignalizerFunctor.ElementaryComplements
public import CFSG.Quasithin.EmptyFaithful.S153WJOff
public import CFSG.Quasithin.EmptyFaithful.T1521SJ

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

variable {G : Type} [Group G]

structure RankBound1521 (S L V V' : Subgroup G) : Prop where
  elem : IsElemAbelian 2 V
  le_inf : V ≤ S ⊓ L
  le_inf' : V' ≤ S ⊓ L
  two_lt : 2 * Nat.card ↥(V ⊓ Subgroup.centralizer (L : Set G)) < Nat.card V
  card_le : ∀ A : Subgroup G, IsElemAbelian 2 A → A ≤ Subgroup.normalizer (L : Set G) →
    A ≤ Subgroup.normalizer ((S ⊓ L : Subgroup G) : Set G) →
      Nat.card A * Nat.card ↥(V ⊓ Subgroup.centralizer (L : Set G)) ≤
        Nat.card ↥(A ⊓ Subgroup.centralizer (L : Set G)) * Nat.card V
  le_sup_of_eq : ∀ A : Subgroup G, IsElemAbelian 2 A → A ≤ Subgroup.normalizer (L : Set G) →
    A ≤ Subgroup.normalizer ((S ⊓ L : Subgroup G) : Set G) →
      Nat.card A * Nat.card ↥(V ⊓ Subgroup.centralizer (L : Set G)) =
          Nat.card ↥(A ⊓ Subgroup.centralizer (L : Set G)) * Nat.card V →
        A ≤ V ⊔ Subgroup.centralizer (L : Set G) ∨ A ≤ V' ⊔ Subgroup.centralizer (L : Set G)

theorem le_innerPart_of_le_sup {S L X A : Subgroup G} (hXL : X ≤ S ⊓ L) (hAS : A ≤ S)
    (h : A ≤ X ⊔ Subgroup.centralizer (L : Set G)) : A ≤ innerPart1521 S L := by
  have hXN : X ≤ Subgroup.normalizer (Subgroup.centralizer (L : Set G) : Set G) :=
    CFSG.Quasithin.B2F.le_normalizer_centralizer
      ((hXL.trans inf_le_right).trans Subgroup.le_normalizer)
  intro a ha
  have h1 : a ∈ ((X ⊔ Subgroup.centralizer (L : Set G) : Subgroup G) : Set G) := h ha
  rw [Subgroup.coe_mul_of_left_le_normalizer_right X _ hXN] at h1
  obtain ⟨x, hx, c, hc, rfl⟩ := h1
  have hxS : x ∈ S := (hXL hx).1
  have hcS : c ∈ S := by
    have := S.mul_mem (S.inv_mem hxS) (hAS ha)
    simpa using this
  exact Subgroup.mul_mem_sup (hXL hx) ⟨hcS, hc⟩

theorem exists_complement_of_isElemAbelian1521 {V Z : Subgroup G} (hV : IsElemAbelian 2 V)
    (hZV : Z ≤ V) : ∃ D : Subgroup G, D ≤ V ∧ Z ⊓ D = ⊥ ∧ Z ⊔ D = V := by
  have : IsMulCommutative V := hV.1
  let _ : CommGroup V := { (inferInstance : Group V) with mul_comm := mul_comm' }
  obtain ⟨C', hC'⟩ := CFSG.SignalizerFunctor.Helpers.elementary_abelian_isCompl_exists 2
    Nat.prime_two V (fun x => Subtype.ext (by simpa using hV.2 x x.2)) (Z.subgroupOf V)
  refine ⟨C'.map V.subtype, Subgroup.map_subtype_le _, ?_, ?_⟩
  · rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxF, c, hc, rfl⟩ := Subgroup.mem_inf.mp hx
    have hcF : c ∈ Z.subgroupOf V := hxF
    have : c ∈ Z.subgroupOf V ⊓ C' := Subgroup.mem_inf.mpr ⟨hcF, hc⟩
    rw [hC'.disjoint.eq_bot, Subgroup.mem_bot] at this
    simp [this]
  · refine le_antisymm (sup_le hZV (Subgroup.map_subtype_le _)) fun a ha => ?_
    have h1 : (⟨a, ha⟩ : V) ∈ Z.subgroupOf V ⊔ C' := by
      rw [hC'.sup_eq_top]
      trivial
    obtain ⟨x, hx, y, hy, hxy⟩ := Subgroup.mem_sup.mp h1
    have : a = (x : G) * (y : G) := by
      have := congrArg Subtype.val hxy
      exact this.symm
    rw [this]
    exact Subgroup.mul_mem_sup hx ⟨y, hy, rfl⟩

theorem conjByElt_one_eq (K : Subgroup G) : conjByElt 1 K = K := by
  ext x
  rw [mem_conjByElt]
  simp

theorem conjByElt_mul_eq (s t : G) (K : Subgroup G) :
    conjByElt (s * t) K = conjByElt s (conjByElt t K) := by
  ext x
  rw [mem_conjByElt, mem_conjByElt, mem_conjByElt]
  rw [mul_inv_rev]
  group

theorem mem_normalizer_of_conjByElt_eq' {y : G} {L : Subgroup G} (h : conjByElt y L = L) :
    y ∈ Subgroup.normalizer (L : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  have h1 := mem_conjByElt (t := y) (x := y * x * y⁻¹) (K := L)
  rw [h] at h1
  have h2 : y⁻¹ * (y * x * y⁻¹) * y = x := by group
  rw [h2] at h1
  exact h1.symm

theorem isElemAbelian_conjByElt' {V : Subgroup G} (hV : IsElemAbelian 2 V) (a : G) :
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

variable [Finite G]

theorem le_innerPart_of_isMaxElemAbelian {S L V V' A : Subgroup G} (hB : RankBound1521 S L V V')
    (hA : IsMaxElemAbelian S A) (hAN : A ≤ Subgroup.normalizer (L : Set G)) :
    A ≤ innerPart1521 S L := by
  have hAS : A ≤ S := hA.1
  have hAP : A ≤ Subgroup.normalizer ((S ⊓ L : Subgroup G) : Set G) :=
    CFSG.Quasithin.B2F.le_normalizer_inf (hAS.trans Subgroup.le_normalizer) hAN
  have hcomm : ∀ x ∈ V, ∀ y ∈ A ⊓ Subgroup.centralizer (L : Set G), x * y = y * x :=
    fun x hx y hy => Subgroup.mem_centralizer_iff.mp hy.2 x (hB.le_inf hx).2
  have hWe : IsElemAbelian 2 (V ⊔ A ⊓ Subgroup.centralizer (L : Set G)) :=
    CFSG.Quasithin.B2F.isElemAbelian_sup_of_commute hB.elem
      (CFSG.Quasithin.B2F.isElemAbelian_mono inf_le_left hA.2.1) hcomm
  have hWS : V ⊔ A ⊓ Subgroup.centralizer (L : Set G) ≤ S :=
    sup_le ((hB.le_inf).trans inf_le_left) (inf_le_left.trans hAS)
  have hWcard := CFSG.Quasithin.B2F.card_sup_mul_card_inf_of_commute hcomm
  have hZle : Nat.card ↥(V ⊓ (A ⊓ Subgroup.centralizer (L : Set G))) ≤
      Nat.card ↥(V ⊓ Subgroup.centralizer (L : Set G)) :=
    Subgroup.card_le_of_le (inf_le_inf_left V inf_le_right)
  have hWA : Nat.card ↥(V ⊔ A ⊓ Subgroup.centralizer (L : Set G)) ≤ Nat.card A :=
    hA.2.2 _ hWS hWe
  have hge : Nat.card ↥(A ⊓ Subgroup.centralizer (L : Set G)) * Nat.card V ≤
      Nat.card A * Nat.card ↥(V ⊓ Subgroup.centralizer (L : Set G)) := by
    rw [mul_comm, ← hWcard]
    exact Nat.mul_le_mul hWA hZle
  have hle := hB.card_le A hA.2.1 hAN hAP
  rcases hB.le_sup_of_eq A hA.2.1 hAN hAP (le_antisymm hle hge) with h | h
  · exact le_innerPart_of_le_sup hB.le_inf hAS h
  · exact le_innerPart_of_le_sup hB.le_inf' hAS h

theorem thompsonJ_le_innerPart_of_bound {S L V V' : Subgroup G} (hB : RankBound1521 S L V V')
    (hSN : S ≤ Subgroup.normalizer (L : Set G)) : thompsonJ S ≤ innerPart1521 S L :=
  iSup₂_le fun _ hA => le_innerPart_of_isMaxElemAbelian hB hA (hA.1.trans hSN)

theorem le_normalizer_of_wreath_aux {S L D : Subgroup G} (hDe : IsElemAbelian 2 D)
    (hDS : D ≤ S ⊓ L) (hDC : D ⊓ Subgroup.centralizer (L : Set G) = ⊥) (hD2 : 2 < Nat.card D)
    (hbound : ∀ A : Subgroup G, IsElemAbelian 2 A → A ≤ Subgroup.normalizer (L : Set G) →
      A ≤ Subgroup.normalizer ((S ⊓ L : Subgroup G) : Set G) →
        Nat.card A ≤ Nat.card D * Nat.card ↥(A ⊓ Subgroup.centralizer (L : Set G)))
    {t : G} (hset : conjSubgroupsBy S L = {L, conjByElt t L}) (hcomm : ⁅L, conjByElt t L⁆ = ⊥)
    {A : Subgroup G} (hA : IsMaxElemAbelian S A) : A ≤ Subgroup.normalizer (L : Set G) := by
  classical
  by_contra hAnot
  obtain ⟨a, haA, han⟩ : ∃ a ∈ A, a ∉ Subgroup.normalizer (L : Set G) := by
    by_contra h
    exact hAnot fun x hx => by
      by_contra hc
      exact h ⟨x, hx, hc⟩
  set C : Subgroup G := Subgroup.centralizer (L : Set G) with hCdef
  have haS : a ∈ S := hA.1 haA
  have hM : ∀ y ∈ S, y ∉ Subgroup.normalizer (L : Set G) → conjByElt y L = conjByElt t L := by
    intro y hy hyn
    have h1 : conjByElt y L ∈ conjSubgroupsBy S L := ⟨y, hy, rfl⟩
    rw [hset] at h1
    rcases h1 with h1 | h1
    · exact absurd (mem_normalizer_of_conjByElt_eq' h1) hyn
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
      apply mem_normalizer_of_conjByElt_eq'
      rw [conjByElt_mul_eq, h1, ← conjByElt_mul_eq, inv_mul_cancel, conjByElt_one_eq]
  have hindexA : Nat.card A ≤ 2 * Nat.card ↥(A ⊓ Subgroup.normalizer (L : Set G)) :=
    W153.card_le_two_mul_of_forall inf_le_left hAcomm haA ha2 hhalf
  have hA₀e : IsElemAbelian 2 (A ⊓ Subgroup.normalizer (L : Set G)) :=
    CFSG.Quasithin.B2F.isElemAbelian_mono inf_le_left hA.2.1
  have hA₀P : A ⊓ Subgroup.normalizer (L : Set G) ≤
      Subgroup.normalizer ((S ⊓ L : Subgroup G) : Set G) :=
    CFSG.Quasithin.B2F.le_normalizer_inf (inf_le_left.trans (hA.1.trans Subgroup.le_normalizer))
      inf_le_right
  have hA₀C : (A ⊓ Subgroup.normalizer (L : Set G)) ⊓ C = A ⊓ C := by
    ext x
    exact ⟨fun hx => ⟨hx.1.1, hx.2⟩, fun hx => ⟨⟨hx.1,
      Subgroup.centralizer_le_normalizer (L : Set G) hx.2⟩, hx.2⟩⟩
  have hbound' := hbound _ hA₀e inf_le_right hA₀P
  rw [hA₀C] at hbound'
  set VM : Subgroup G := conjByElt a D with hVMdef
  have hVMS : VM ≤ S := by
    rintro _ ⟨y, hy, rfl⟩
    exact S.mul_mem (S.mul_mem haS (hDS hy).1) (S.inv_mem haS)
  have hVML : VM ≤ conjByElt t L := by
    rw [← hMa]
    exact Subgroup.map_mono (hDS.trans inf_le_right)
  have hLM : ∀ x ∈ L, ∀ y ∈ conjByElt t L, x * y = y * x := by
    intro x hx y hy
    have hle := Subgroup.commutator_eq_bot_iff_le_centralizer.1 hcomm
    exact (Subgroup.mem_centralizer_iff.1 (hle hx) y hy).symm
  have hcommVM : ∀ x ∈ D, ∀ y ∈ VM, x * y = y * x := fun x hx y hy =>
    hLM x (hDS hx).2 y (hVML hy)
  have hVMe : IsElemAbelian 2 VM := isElemAbelian_conjByElt' hDe a
  have hUe : IsElemAbelian 2 (D ⊔ VM) :=
    CFSG.Quasithin.B2F.isElemAbelian_sup_of_commute hDe hVMe hcommVM
  have hUS : D ⊔ VM ≤ S := sup_le (hDS.trans inf_le_left) hVMS
  have hbot : D ⊓ VM = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have hzC : z ∈ D ⊓ C := ⟨hz.1, Subgroup.mem_centralizer_iff.mpr fun y hy =>
      hLM y hy z (hVML hz.2)⟩
    rw [hDC] at hzC
    exact hzC
  have hVMcard : Nat.card VM = Nat.card D :=
    Subgroup.card_map_of_injective (f := (MulAut.conj a).toMonoidHom) (MulAut.conj a).injective
  have hUcard : Nat.card ↥(D ⊔ VM) = Nat.card D * Nat.card D := by
    have h := CFSG.Quasithin.B2F.card_sup_mul_card_inf_of_commute hcommVM
    rw [hbot, Subgroup.card_bot, mul_one, hVMcard] at h
    exact h
  have hCcomm : ∀ z ∈ A ⊓ C, ∀ x ∈ D ⊔ VM, x * z = z * x := by
    intro z hz x hx
    have hzV : ∀ h ∈ D, h * z = z * h := fun h hh =>
      Subgroup.mem_centralizer_iff.mp hz.2 h (hDS hh).2
    have hzVM : ∀ h ∈ VM, h * z = z * h := by
      rintro _ ⟨v, hv, rfl⟩
      have hab : Commute a z := hAcomm a haA z hz.1
      have hvz : Commute v z := hzV v hv
      exact (((hab.mul_left hvz).mul_left hab.inv_left) : Commute (a * v * a⁻¹) z).eq
    have hle : D ⊔ VM ≤ Subgroup.centralizer ({z} : Set G) := by
      refine sup_le (fun h hh => ?_) (fun h hh => ?_)
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact hzV h hh
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact hzVM h hh
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle hx)
  have hCe : IsElemAbelian 2 (A ⊓ C) := CFSG.Quasithin.B2F.isElemAbelian_mono inf_le_left hA.2.1
  have hWe : IsElemAbelian 2 ((D ⊔ VM) ⊔ A ⊓ C) :=
    CFSG.Quasithin.B2F.isElemAbelian_sup_of_commute hUe hCe fun x hx z hz => hCcomm z hz x hx
  have hWS : (D ⊔ VM) ⊔ A ⊓ C ≤ S := sup_le hUS (inf_le_left.trans hA.1)
  have hbot2 : (D ⊔ VM) ⊓ (A ⊓ C) = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have hzU : z ∈ ((D ⊔ VM : Subgroup G) : Set G) := hz.1
    have hVN : D ≤ Subgroup.normalizer (VM : Set G) := by
      refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact (hcommVM x hx y hy).symm
    rw [Subgroup.coe_mul_of_left_le_normalizer_right D _ hVN] at hzU
    obtain ⟨x, hx, y, hy, rfl⟩ := hzU
    have hyC : y ∈ C := Subgroup.mem_centralizer_iff.mpr fun l hl =>
      hLM l hl y (hVML hy)
    have hxC : x ∈ C := by
      have := C.mul_mem hz.2.2 (C.inv_mem hyC)
      simpa using this
    have hxV : x ∈ D ⊓ C := ⟨hx, hxC⟩
    rw [hDC] at hxV
    have hx1 : x = 1 := hxV
    subst hx1
    obtain ⟨v, hv, rfl⟩ := hy
    have hcz : a * (1 * (a * v * a⁻¹)) * a⁻¹ = 1 * (a * v * a⁻¹) := by
      have := hAcomm a haA _ hz.2.1
      rw [mul_inv_eq_iff_eq_mul]
      exact this
    have hvv : v = a * v * a⁻¹ := by
      have e : a * (1 * (a * v * a⁻¹)) * a⁻¹ = (a * a) * v * (a * a)⁻¹ := by group
      rw [e, ha2] at hcz
      simpa using hcz
    have hvVM : v ∈ VM := by
      refine ⟨v, hv, ?_⟩
      exact hvv.symm
    have : v ∈ D ⊓ VM := ⟨hv, hvVM⟩
    rw [hbot] at this
    have hv1 : v = 1 := this
    subst hv1
    simp
  have hWcard : Nat.card ↥((D ⊔ VM) ⊔ A ⊓ C) =
      Nat.card ↥(D ⊔ VM) * Nat.card ↥(A ⊓ C) := by
    have h := CFSG.Quasithin.B2F.card_sup_mul_card_inf_of_commute
      (fun x hx z hz => hCcomm z hz x hx)
    rw [hbot2, Subgroup.card_bot, mul_one] at h
    exact h
  have hWA : Nat.card ↥((D ⊔ VM) ⊔ A ⊓ C) ≤ Nat.card A := hA.2.2 _ hWS hWe
  rw [hWcard, hUcard] at hWA
  have hCpos : 0 < Nat.card ↥(A ⊓ C) := Nat.card_pos
  have hVpos : 0 < Nat.card D := Nat.card_pos
  have h2 : Nat.card D * (Nat.card D * Nat.card ↥(A ⊓ C)) ≤
      2 * (Nat.card D * Nat.card ↥(A ⊓ C)) := by
    calc Nat.card D * (Nat.card D * Nat.card ↥(A ⊓ C))
        = Nat.card D * Nat.card D * Nat.card ↥(A ⊓ C) := by ring
      _ ≤ Nat.card A := hWA
      _ ≤ 2 * Nat.card ↥(A ⊓ Subgroup.normalizer (L : Set G)) := hindexA
      _ ≤ 2 * (Nat.card D * Nat.card ↥(A ⊓ C)) := Nat.mul_le_mul_left 2 hbound'
  have h3 : Nat.card D ≤ 2 := Nat.le_of_mul_le_mul_right h2 (Nat.mul_pos hVpos hCpos)
  exact absurd hD2 (not_lt.mpr h3)

theorem le_normalizer_of_wreath_bound {S L V V' : Subgroup G} (hB : RankBound1521 S L V V')
    {t : G} (hset : conjSubgroupsBy S L = {L, conjByElt t L}) (hcomm : ⁅L, conjByElt t L⁆ = ⊥)
    {A : Subgroup G} (hA : IsMaxElemAbelian S A) : A ≤ Subgroup.normalizer (L : Set G) := by
  set C : Subgroup G := Subgroup.centralizer (L : Set G) with hCdef
  obtain ⟨D, hDV, hZD, hZDV⟩ :=
    exists_complement_of_isElemAbelian1521 hB.elem (inf_le_left : V ⊓ C ≤ V)
  have hDe : IsElemAbelian 2 D := CFSG.Quasithin.B2F.isElemAbelian_mono hDV hB.elem
  have hVcard : Nat.card ↥(V ⊓ C) * Nat.card D = Nat.card V := by
    have hc : ∀ a ∈ V ⊓ C, ∀ b ∈ D, a * b = b * a := fun a ha b hb =>
      CFSG.Quasithin.B2F.isElemAbelian_comm hB.elem ha.1 (hDV hb)
    have h := CFSG.Quasithin.B2F.card_sup_mul_card_inf_of_commute hc
    rw [hZD, Subgroup.card_bot, mul_one, hZDV] at h
    exact h.symm
  have hZpos : 0 < Nat.card ↥(V ⊓ C) := Nat.card_pos
  have hD2 : 2 < Nat.card D := by
    have h := hB.two_lt
    rw [← hVcard, mul_comm 2] at h
    exact Nat.lt_of_mul_lt_mul_left h
  have hDC : D ⊓ C = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hx' : x ∈ (V ⊓ C) ⊓ D := ⟨⟨hDV hx.1, hx.2⟩, hx.1⟩
    rw [hZD] at hx'
    exact hx'
  refine le_normalizer_of_wreath_aux hDe (hDV.trans hB.le_inf) hDC hD2 ?_ hset hcomm hA
  intro A₀ hA₀e hA₀L hA₀P
  have h := hB.card_le A₀ hA₀e hA₀L hA₀P
  have h' : Nat.card A₀ * Nat.card ↥(V ⊓ C) ≤
      (Nat.card D * Nat.card ↥(A₀ ⊓ C)) * Nat.card ↥(V ⊓ C) := by
    calc Nat.card A₀ * Nat.card ↥(V ⊓ C) ≤ Nat.card ↥(A₀ ⊓ C) * Nat.card V := h
      _ = Nat.card ↥(A₀ ⊓ C) * (Nat.card ↥(V ⊓ C) * Nat.card D) := by rw [hVcard]
      _ = (Nat.card D * Nat.card ↥(A₀ ⊓ C)) * Nat.card ↥(V ⊓ C) := by ring
  exact Nat.le_of_mul_le_mul_right h' hZpos

theorem thompsonJ_le_innerPart_of_bound_wreath {S L V V' : Subgroup G}
    (hB : RankBound1521 S L V V') {t : G}
    (hset : conjSubgroupsBy S L = {L, conjByElt t L}) (hcomm : ⁅L, conjByElt t L⁆ = ⊥) :
    thompsonJ S ≤ innerPart1521 S L :=
  iSup₂_le fun _ hA => le_innerPart_of_isMaxElemAbelian hB hA
    (le_normalizer_of_wreath_bound hB hset hcomm hA)

end CFSG.Quasithin
