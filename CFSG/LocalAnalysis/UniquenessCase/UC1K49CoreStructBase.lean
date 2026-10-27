module

public import CFSG.LocalAnalysis.UniquenessCase.UC1K49CoreStructLin

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC49

variable {G : Type} [Group G] [Finite G]

open scoped commutatorElement IsMulCommutative
open CFSG.ABGLocalTools

theorem commutator_sup_le_of_normal49 {Q A B E : Subgroup G}
    (hAB : A ≤ Subgroup.normalizer (B : Set G))
    (hAE : A ≤ Subgroup.normalizer (E : Set G)) (hBE : B ≤ Subgroup.normalizer (E : Set G))
    (hA : ⁅Q, A⁆ ≤ E) (hB : ⁅Q, B⁆ ≤ E) : ⁅Q, A ⊔ B⁆ ≤ E := by
  rw [Subgroup.commutator_le]
  intro q hq g hg
  obtain ⟨a, ha, b, hb, rfl⟩ := (mem_sup_of_le_normalizer hAB).mp hg
  have hqa : ⁅q, a⁆ ∈ E := (Subgroup.commutator_le.mp hA) q hq a ha
  have hqb : ⁅q, b⁆ ∈ E := (Subgroup.commutator_le.mp hB) q hq b hb
  have hconj : a * ⁅q, b⁆ * a⁻¹ ∈ E :=
    (Subgroup.mem_normalizer_iff.mp (hAE ha) ⁅q, b⁆).mp hqb
  rw [commutatorElement_mul_right_eq_mul_conj,
    show ⁅q, a⁆ * a * ⁅q, b⁆ * a⁻¹ = ⁅q, a⁆ * (a * ⁅q, b⁆ * a⁻¹) by group]
  exact E.mul_mem hqa hconj

theorem le_normalizer_commutator49 {S A B : Subgroup G}
    (hA : S ≤ Subgroup.normalizer (A : Set G)) (hB : S ≤ Subgroup.normalizer (B : Set G)) :
    S ≤ Subgroup.normalizer (⁅A, B⁆ : Subgroup G) := by
  intro s hs
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  rw [Subgroup.map_commutator, Subgroup.mem_normalizer_iff_map_conj_eq.mp (hA hs),
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hB hs)]

theorem normal_eq_top_of_isAlt_five {G : Type} [Group G]
    (hG : CFSG.LocalAnalysis.UniquenessCase.UC22.IsAlt G 5)
    {H : Subgroup G} [H.Normal] {a : G} (ha : a ∈ H) (ha1 : a ≠ 1) : H = ⊤ := by
  obtain ⟨e⟩ := hG
  haveI hHmap : (H.map e.toMonoidHom).Normal :=
    (inferInstance : H.Normal).map e.toMonoidHom e.surjective
  have hneq : H.map e.toMonoidHom ≠ ⊥ := by
    intro hbot
    have hmem : e a ∈ (⊥ : Subgroup (alternatingGroup (Fin 5))) := by
      rw [← hbot]
      exact Subgroup.mem_map_of_mem e.toMonoidHom ha
    rw [Subgroup.mem_bot] at hmem
    exact ha1 (e.injective (by simpa using hmem))
  have htop : H.map e.toMonoidHom = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (H.map e.toMonoidHom) with h | h
    · exact absurd h hneq
    · exact h
  rw [eq_top_iff]
  intro g _
  have hmem : e g ∈ H.map e.toMonoidHom := by rw [htop]; exact Subgroup.mem_top _
  obtain ⟨h, hh, hhe⟩ := Subgroup.mem_map.mp hmem
  have hgh : g = h := (e.injective hhe).symm
  rw [hgh]
  exact hh

theorem eq_top_of_isAlt_five_quotient {Γ : Type} [Group Γ] {K O L : Subgroup Γ}
    (hKL : K ≤ L) (hKnorm : L ≤ Subgroup.normalizer (K : Set Γ))
    (hOK : O ≤ K) (hOeq : O.subgroupOf L = CFSG.pCore 2 ↥L)
    (hLalt : IsAlt (Bar2 L) 5) (hex : ∃ a ∈ K, a ∉ O) : K = L := by
  let q : ↥L →* ↥L ⧸ CFSG.pCore 2 ↥L := QuotientGroup.mk' (CFSG.pCore 2 ↥L)
  let K' : Subgroup ↥L := K.subgroupOf L
  haveI hK'norm : K'.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hKL).mpr hKnorm
  have hK'map : (K'.map q).Normal := hK'norm.map q (QuotientGroup.mk'_surjective _)
  obtain ⟨a, haK, haO⟩ := hex
  have haL : a ∈ L := hKL haK
  have haK' : (⟨a, haL⟩ : ↥L) ∈ K' := Subgroup.mem_subgroupOf.mpr haK
  have hqa_mem : q ⟨a, haL⟩ ∈ K'.map q := Subgroup.mem_map_of_mem q haK'
  have hqa_ne : q ⟨a, haL⟩ ≠ 1 := by
    intro h1
    apply haO
    have hker : (⟨a, haL⟩ : ↥L) ∈ CFSG.pCore 2 ↥L := by
      rw [← QuotientGroup.ker_mk' (CFSG.pCore 2 ↥L), MonoidHom.mem_ker]; exact h1
    rw [← hOeq] at hker
    exact Subgroup.mem_subgroupOf.mp hker
  haveI : (K'.map q).Normal := hK'map
  have hHtop : K'.map q = ⊤ := normal_eq_top_of_isAlt_five hLalt hqa_mem hqa_ne
  have hK'top : K' = ⊤ := by
    rw [eq_top_iff]
    intro l hl
    have hql : q l ∈ K'.map q := by rw [hHtop]; exact Subgroup.mem_top _
    obtain ⟨k, hk, hkq⟩ := Subgroup.mem_map.mp hql
    have hkl_ker : (k⁻¹ * l : ↥L) ∈ CFSG.pCore 2 ↥L := by
      rw [← QuotientGroup.ker_mk' (CFSG.pCore 2 ↥L)]
      rw [MonoidHom.mem_ker]
      rw [map_mul, map_inv, hkq, inv_mul_cancel]
    rw [← hOeq] at hkl_ker
    have hklK : (k⁻¹ * l : ↥L) ∈ K' :=
      Subgroup.mem_subgroupOf.mpr (hOK (Subgroup.mem_subgroupOf.mp hkl_ker))
    have : l = k * (k⁻¹ * l) := by group
    rw [this]
    exact K'.mul_mem hk hklK
  have hLK : L ≤ K := (Subgroup.subgroupOf_eq_top).mp hK'top
  exact le_antisymm hKL hLK

theorem chief_struct49_rho_commute_of_Q {H X L Q I : Subgroup G} (h : Setup49 H X L Q I)
    {N M : Subgroup G} (hch : HChief H N M) (hNQ : N ≤ Q)
    [hNorm : (M.subgroupOf N).Normal] [hElem : IsElementaryAbelian 2 (N ⧸ M.subgroupOf N)]
    {u v : ↥H} (huv : ⁅(u : G), (v : G)⁆ ∈ Q) :
    (chiefRep (p := 2) hch.2.1 hch.2.2.1 u).val *
        (chiefRep (p := 2) hch.2.1 hch.2.2.1 v).val =
      (chiefRep (p := 2) hch.2.1 hch.2.2.1 v).val *
        (chiefRep (p := 2) hch.2.1 hch.2.2.1 u).val := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let ρ : H →* LinearMap.GeneralLinearGroup (ZMod 2) (Additive (N ⧸ M.subgroupOf N)) :=
    chiefRep (p := 2) hch.2.1 hch.2.2.1
  have hQH : Q ≤ H := Q_le_H49 h
  let w : ↥H := ⟨⁅(u : G), (v : G)⁆, hQH huv⟩
  have hw_eq : w = ⁅u, v⁆ := by
    apply Subtype.ext
    rfl
  have hcomm : ⁅ρ u, ρ v⁆ = 1 := by
    have hmap := map_commutatorElement ρ u v
    rw [← hw_eq] at hmap
    rw [← hmap]
    have : ρ w = 1 := by
      apply (chiefRep_eq_one_iff (p := 2) hch.2.1 hch.2.2.1 w).mpr
      intro nn hn
      have hc : ⁅nn, (w : G)⁆ ∈ M :=
        (Subgroup.commutator_le.mp (chief_q_trivial49 h hch hNQ)) nn hn (w : G) huv
      simpa using hc
    exact this
  have hcomm' : ρ u * ρ v = ρ v * ρ u := commutatorElement_eq_one_iff_commute.mp hcomm
  calc (ρ u).val * (ρ v).val = (ρ u * ρ v).val := (Units.val_mul _ _).symm
    _ = (ρ v * ρ u).val := by rw [hcomm']
    _ = (ρ v).val * (ρ u).val := Units.val_mul _ _

private theorem base_chiefRep_mem_Q_apply {H X L Q I : Subgroup G} (h : Setup49 H X L Q I)
    {N M : Subgroup G} (hch : HChief H N M) (hNQ : N ≤ Q)
    [hNorm : (M.subgroupOf N).Normal] [hElem : IsElementaryAbelian 2 (N ⧸ M.subgroupOf N)]
    {g : ↥H} (hgQ : (g : G) ∈ Q) (v : Additive (N ⧸ M.subgroupOf N)) :
    (chiefRep (p := 2) hch.2.1 hch.2.2.1 g).val v = v := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : chiefRep (p := 2) hch.2.1 hch.2.2.1 g = 1 := by
    apply (chiefRep_eq_one_iff (p := 2) hch.2.1 hch.2.2.1 g).mpr
    intro n hn
    exact (Subgroup.commutator_le.mp (chief_q_trivial49 h hch hNQ)) n hn (g : G) hgQ
  rw [show (chiefRep (p := 2) hch.2.1 hch.2.2.1 g).val = 1 by
    simpa using congrArg Units.val h1]
  simp

private noncomputable def base_LkAction {H' : Type} [Group H'] {V : Type*} [AddCommGroup V]
    [Module (ZMod 2) V] (ρ : H' →* LinearMap.GeneralLinearGroup (ZMod 2) V)
    {Lk : Subgroup G} (incl : ↥Lk →* H') (W : Submodule (ZMod 2) V)
    (hW : ∀ g : ↥Lk, ∀ w ∈ W, (ρ (incl g)).val w ∈ W) :
    ↥Lk →* Module.End (ZMod 2) W where
  toFun g := ((ρ (incl g)).val).restrict (hW g)
  map_one' := by
    ext w
    simp
  map_mul' := by
    intro a b
    ext w
    simp only [LinearMap.restrict_apply, Module.End.mul_apply, map_mul, Units.val_mul]

private theorem base_normal_eq_top_of_pCore_lt {L : Type} [Group L]
    (hLalt : IsAlt (L ⧸ CFSG.pCore 2 L) 5) {K : Subgroup L} [K.Normal]
    (hpcore : CFSG.pCore 2 L ≤ K) {a : L} (ha : a ∈ K)
    (hane : (QuotientGroup.mk' (CFSG.pCore 2 L) a : L ⧸ CFSG.pCore 2 L) ≠ 1) :
    K = ⊤ := by
  let q : L →* (L ⧸ CFSG.pCore 2 L) := QuotientGroup.mk' (CFSG.pCore 2 L)
  have htop : K.map q = ⊤ :=
    normal_eq_top_of_isAlt_five hLalt (Subgroup.mem_map_of_mem q ha) hane
  rw [eq_top_iff]
  intro l _
  have hql : q l ∈ K.map q := by rw [htop]; exact Subgroup.mem_top _
  obtain ⟨k, hk, hkq⟩ := Subgroup.mem_map.mp hql
  have hker : l * k⁻¹ ∈ CFSG.pCore 2 L := by
    rw [← QuotientGroup.ker_mk' (CFSG.pCore 2 L), MonoidHom.mem_ker]
    rw [map_mul, map_inv, hkq, mul_inv_cancel]
  have : l = (l * k⁻¹) * k := by group
  rw [this]
  exact K.mul_mem (hpcore hker) hk

private theorem base_mk_ne_one_of_not_mem {Lk Q : Subgroup G} {ak : G}
    (hak : ak ∈ Lk) (hOeq : (Lk ⊓ Q).subgroupOf Lk = CFSG.pCore 2 ↥Lk) (hakQ : ak ∉ Q) :
    (QuotientGroup.mk' (CFSG.pCore 2 ↥Lk) ⟨ak, hak⟩ : ↥Lk ⧸ CFSG.pCore 2 ↥Lk) ≠ 1 := by
  intro h1
  apply hakQ
  have hmem : (⟨ak, hak⟩ : ↥Lk) ∈ CFSG.pCore 2 ↥Lk := by
    rw [← QuotientGroup.ker_mk' (CFSG.pCore 2 ↥Lk), MonoidHom.mem_ker]
    exact h1
  rw [← hOeq] at hmem
  exact (Subgroup.mem_subgroupOf.mp hmem).2

theorem chief_struct49_Lk_trivial_of_invariant {H X L Q I : Subgroup G} (h : Setup49 H X L Q I)
    {N M : Subgroup G} (hch : HChief H N M) (hNQ : N ≤ Q)
    [hNorm : (M.subgroupOf N).Normal] [hElem : IsElementaryAbelian 2 (N ⧸ M.subgroupOf N)]
    {Lk : Subgroup G} {ak : ↥H} (hLkH : Lk ≤ H) (hak : (ak : G) ∈ Lk)
    (hLalt : IsAlt (Bar2 Lk) 5) (hOeq : (Lk ⊓ Q).subgroupOf Lk = CFSG.pCore 2 ↥Lk)
    (hakQ : (ak : G) ∉ Q) (W : Submodule (ZMod 2) (Additive (N ⧸ M.subgroupOf N)))
    (hWinv' : ∀ g : ↥H, (g : G) ∈ Lk → ∀ w ∈ W,
      (chiefRep (p := 2) hch.2.1 hch.2.2.1 g).val w ∈ W)
    (hak_fix : ∀ w ∈ W, (chiefRep (p := 2) hch.2.1 hch.2.2.1 ak).val w = w) :
    ∀ g : ↥H, (g : G) ∈ Lk → ∀ w ∈ W,
      (chiefRep (p := 2) hch.2.1 hch.2.2.1 g).val w = w := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let ρ : H →* LinearMap.GeneralLinearGroup (ZMod 2) (Additive (N ⧸ M.subgroupOf N)) :=
    chiefRep (p := 2) hch.2.1 hch.2.2.1
  have hWinv : ∀ (g : ↥Lk), ∀ w : Additive (N ⧸ M.subgroupOf N), w ∈ W →
      (ρ (Subgroup.inclusion hLkH g)).val w ∈ W :=
    fun g w hw => hWinv' (Subgroup.inclusion hLkH g) g.2 w hw
  let φ : ↥Lk →* Module.End (ZMod 2) W :=
    base_LkAction ρ (Subgroup.inclusion hLkH) W hWinv
  haveI : φ.ker.Normal := MonoidHom.normal_ker φ
  have hpCore : CFSG.pCore 2 ↥Lk ≤ φ.ker := by
    rw [← hOeq]
    intro q' hq'
    rw [MonoidHom.mem_ker]
    change ((ρ (Subgroup.inclusion hLkH q')).val).restrict (hWinv q') = 1
    ext w
    change (ρ (Subgroup.inclusion hLkH q')).val w.1 = w.1
    exact base_chiefRep_mem_Q_apply h hch hNQ (Subgroup.mem_subgroupOf.mp hq').2 w.1
  have hakK' : (⟨ak, hak⟩ : ↥Lk) ∈ φ.ker := by
    rw [MonoidHom.mem_ker]
    ext w
    exact hak_fix w w.2
  have hane : (QuotientGroup.mk' (CFSG.pCore 2 ↥Lk) ⟨ak, hak⟩ : ↥Lk ⧸ CFSG.pCore 2 ↥Lk) ≠ 1 :=
    base_mk_ne_one_of_not_mem hak hOeq hakQ
  have hker : φ.ker = ⊤ := base_normal_eq_top_of_pCore_lt hLalt hpCore hakK' hane
  intro g hg w hw
  have hgker : φ ⟨g, hg⟩ = 1 := by
    have : (⟨g, hg⟩ : ↥Lk) ∈ φ.ker := by rw [hker]; exact Subgroup.mem_top _
    exact this
  have h3 : (ρ g).val w = w :=
    congrArg Subtype.val (congrArg (fun f : Module.End (ZMod 2) W => f ⟨w, hw⟩) hgker)
  exact h3

theorem chief_struct49_fixed_I_invariant {H X L Q I : Subgroup G} (h : Setup49 H X L Q I)
    {N M : Subgroup G} (hch : HChief H N M)
    [hNorm : (M.subgroupOf N).Normal] [hElem : IsElementaryAbelian 2 (N ⧸ M.subgroupOf N)] :
    ∀ n : ↥H, ∀ v : Additive (N ⧸ M.subgroupOf N),
      (∀ g : ↥I,
        (chiefRep (p := 2) hch.2.1 hch.2.2.1 (Subgroup.inclusion (I_le_H h) g)).val v = v) →
      (∀ g : ↥I, (chiefRep (p := 2) hch.2.1 hch.2.2.1 (Subgroup.inclusion (I_le_H h) g)).val
        ((chiefRep (p := 2) hch.2.1 hch.2.2.1 n).val v) =
        (chiefRep (p := 2) hch.2.1 hch.2.2.1 n).val v) := by
  intro n v hv g
  let ρ : H →* LinearMap.GeneralLinearGroup (ZMod 2) (Additive (N ⧸ M.subgroupOf N)) :=
    chiefRep (p := 2) hch.2.1 hch.2.2.1
  have hconj : (n : G)⁻¹ * (g : G) * (n : G) ∈ I := by
    have := (Subgroup.mem_normalizer_iff.mp
      (le_normalizer_I h (Subgroup.inv_mem _ n.2)) (g : G)).mp g.2
    simpa using this
  let g' : ↥I := ⟨(n : G)⁻¹ * (g : G) * (n : G), hconj⟩
  have hg'v : (ρ (Subgroup.inclusion (I_le_H h) g')).val v = v := hv g'
  have hprod : Subgroup.inclusion (I_le_H h) g' =
      n⁻¹ * Subgroup.inclusion (I_le_H h) g * n := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inclusion, g']
  have hρg' : ρ (Subgroup.inclusion (I_le_H h) g') =
      (ρ n)⁻¹ * ρ (Subgroup.inclusion (I_le_H h) g) * ρ n := by
    rw [hprod, map_mul, map_mul, map_inv]
  have h3 := congrArg (ρ n).val hg'v
  have h4 : (ρ (Subgroup.inclusion (I_le_H h) g')).val =
      ((ρ n)⁻¹).val * (ρ (Subgroup.inclusion (I_le_H h) g)).val * (ρ n).val := by
    rw [hρg', Units.val_mul, Units.val_mul]
  rw [h4, Module.End.mul_apply, Module.End.mul_apply] at h3
  have h5 : (ρ n).val * ((ρ n)⁻¹).val = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  rw [← Module.End.mul_apply, h5, Module.End.one_apply] at h3
  exact h3

def CV_I {H X L Q I : Subgroup G} (h : Setup49 H X L Q I) {N M : Subgroup G}
    (hch : HChief H N M)
    [hNorm : (M.subgroupOf N).Normal] [hElem : IsElementaryAbelian 2 (N ⧸ M.subgroupOf N)] :
    Submodule (ZMod 2) (Additive (N ⧸ M.subgroupOf N)) where
  carrier := {v | ∀ g : ↥I, ((chiefRep (p := 2) hch.2.1 hch.2.2.1
    (Subgroup.inclusion (I_le_H h) g)).val) v = v}
  zero_mem' := by intro g; simp
  add_mem' := by intro a b ha hb g; simp only [map_add, ha g, hb g]
  smul_mem' := by intro c a ha g; simp only [map_smul, ha g]

theorem CV_I_eq_bot {H X L Q I : Subgroup G} (h : Setup49 H X L Q I)
    {N M : Subgroup G} (hch : HChief H N M) (hI : ¬ ⁅N, I⁆ ≤ M)
    [hNorm : (M.subgroupOf N).Normal] [hElem : IsElementaryAbelian 2 (N ⧸ M.subgroupOf N)] :
    CV_I h hch = ⊥ := by
  have hInv : ∀ n : ↥H, ∀ v : Additive (N ⧸ M.subgroupOf N), v ∈ CV_I h hch →
      ((chiefRep (p := 2) hch.2.1 hch.2.2.1 n).val) v ∈ CV_I h hch :=
    fun n v hv => chief_struct49_fixed_I_invariant h hch n v hv
  rcases chiefRep_irreducible hch (CV_I h hch) hInv with hbot | htop
  · exact hbot
  · exfalso
    apply hI
    rw [Subgroup.commutator_le]
    intro nn hn g hg
    have hgtriv : (chiefRep (p := 2) hch.2.1 hch.2.2.1
        (Subgroup.inclusion (I_le_H h) ⟨g, hg⟩)) = 1 := by
      apply Units.ext
      ext v
      have hv : v ∈ CV_I h hch := by rw [htop]; exact Submodule.mem_top
      exact hv ⟨g, hg⟩
    have := (chiefRep_eq_one_iff (p := 2) hch.2.1 hch.2.2.1
      (Subgroup.inclusion (I_le_H h) ⟨g, hg⟩)).mp hgtriv nn hn
    simpa using this

section Operators

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

theorem pairwise_commute_triple {a b c : Module.End (ZMod 2) V} (hab : a * b = b * a)
    (hac : a * c = c * a) (hbc : b * c = c * b) :
    ({a, b, c} : Set (Module.End (ZMod 2) V)).Pairwise Commute :=
  (Set.pairwise_insert_of_symm_of_refl).2 ⟨pairwise_commute_pair hbc, fun d hd => by
    rcases hd with rfl | hd
    · exact hab
    · rw [Set.mem_singleton_iff] at hd
      subst hd
      exact hac⟩

@[expose] def TrivOn (W : Submodule (ZMod 2) V) (T : Module.End (ZMod 2) V) : Prop :=
  ∀ x ∈ W, T x = x

@[expose] def FpfOn (W : Submodule (ZMod 2) V) (T : Module.End (ZMod 2) V) : Prop :=
  ∀ x ∈ W, T x = x → x = 0

structure Wt49 (A0 A1 A2 X Xi S Si : Module.End (ZMod 2) V) : Prop where
  cube0 : A0 ^ 3 = 1
  cube1 : A1 ^ 3 = 1
  cube2 : A2 ^ 3 = 1
  comm01 : A0 * A1 = A1 * A0
  comm02 : A0 * A2 = A2 * A0
  comm12 : A1 * A2 = A2 * A1
  XiX : Xi * X = 1
  XXi : X * Xi = 1
  rot0 : Xi * A0 * X = A1
  rot1 : Xi * A1 * X = A2
  rot2 : Xi * A2 * X = A0
  SiS : Si * S = 1
  SSi : S * Si = 1
  inv0 : Si * A0 * S = A0 ^ 2
  fix1 : Si * A1 * S = A1
  fix2 : Si * A2 * S = A2
  ne_one : A0 * A1 * A2 ≠ 1
  card_le : Nat.card V ≤ 64 * Nat.card {v : V // (A0 * A1 * A2) v = v}

@[expose] def Uz (A0 A1 A2 : Module.End (ZMod 2) V) : Submodule (ZMod 2) V :=
  LinearMap.ker (e2 (A0 * A1 * A2))

@[expose] def Wb (A0 A1 A2 : Module.End (ZMod 2) V) : Submodule (ZMod 2) V :=
  LinearMap.range (e2 (A0 * A1 ^ 2)) ⊓ Uz A0 A1 A2

@[expose] def Wbz (A0 A1 A2 : Module.End (ZMod 2) V) : Submodule (ZMod 2) V :=
  LinearMap.range (e2 (A0 * A1 ^ 2 * (A0 * A1 * A2))) ⊓ Uz A0 A1 A2

@[expose] def Wbz2 (A0 A1 A2 : Module.End (ZMod 2) V) : Submodule (ZMod 2) V :=
  LinearMap.range (e2 (A0 * A1 ^ 2 * (A0 * A1 * A2) ^ 2)) ⊓ Uz A0 A1 A2

@[expose] def PatI (A0 A1 A2 : Module.End (ZMod 2) V) : Prop :=
  (TrivOn (Wb A0 A1 A2) A0 ∧ TrivOn (Wb A0 A1 A2) A1 ∧ FpfOn (Wb A0 A1 A2) A2) ∧
  (TrivOn (Wbz A0 A1 A2) A0 ∧ FpfOn (Wbz A0 A1 A2) A1 ∧ TrivOn (Wbz A0 A1 A2) A2) ∧
  (FpfOn (Wbz2 A0 A1 A2) A0 ∧ TrivOn (Wbz2 A0 A1 A2) A1 ∧ TrivOn (Wbz2 A0 A1 A2) A2)

@[expose] def PatIIa (A0 A1 A2 : Module.End (ZMod 2) V) : Prop :=
  (FpfOn (Wb A0 A1 A2) A0 ∧ FpfOn (Wb A0 A1 A2) A1 ∧ TrivOn (Wb A0 A1 A2) A2) ∧
  (FpfOn (Wbz A0 A1 A2) A0 ∧ TrivOn (Wbz A0 A1 A2) A1 ∧ FpfOn (Wbz A0 A1 A2) A2) ∧
  (TrivOn (Wbz2 A0 A1 A2) A0 ∧ FpfOn (Wbz2 A0 A1 A2) A1 ∧ FpfOn (Wbz2 A0 A1 A2) A2)

@[expose] def PatIIb (A0 A1 A2 : Module.End (ZMod 2) V) : Prop :=
  (FpfOn (Wb A0 A1 A2) A0 ∧ FpfOn (Wb A0 A1 A2) A1 ∧ FpfOn (Wb A0 A1 A2) A2) ∧
  (FpfOn (Wbz A0 A1 A2) A0 ∧ FpfOn (Wbz A0 A1 A2) A1 ∧ FpfOn (Wbz A0 A1 A2) A2) ∧
  (FpfOn (Wbz2 A0 A1 A2) A0 ∧ FpfOn (Wbz2 A0 A1 A2) A1 ∧ FpfOn (Wbz2 A0 A1 A2) A2)

@[expose] def Disj49 (A0 A1 A2 : Module.End (ZMod 2) V) : Prop :=
  LinearMap.range (e2 A0) ⊓ LinearMap.range (e2 A1) = ⊥ ∧
    LinearMap.range (e2 A0) ⊓ LinearMap.range (e2 A2) = ⊥ ∧
    LinearMap.range (e2 A1) ⊓ LinearMap.range (e2 A2) = ⊥

end Operators

section OperatorLemmas

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
variable {A0 A1 A2 X Xi S Si : Module.End (ZMod 2) V}

theorem Wt49.rels (hW : Wt49 A0 A1 A2 X Xi S Si) :
    (A0 * A1 ^ 2) ^ 3 = 1 ∧ (A0 * A1 * A2) ^ 3 = 1 ∧
      (A0 * A1 ^ 2) * (A0 * A1 * A2) = (A0 * A1 * A2) * (A0 * A1 ^ 2) ∧
      (A0 * A1 ^ 2) * (A0 * A1 * A2) = A0 ^ 2 * A2 ∧
      (A0 * A1 ^ 2) * (A0 * A1 * A2) ^ 2 = A1 * A2 ^ 2 := by
  let T : Subring (Module.End (ZMod 2) V) := Subring.closure ({A0, A1, A2} : Set _)
  letI : CommRing T := Subring.closureCommRingOfComm
    (pairwise_commute_triple hW.comm01 hW.comm02 hW.comm12)
  let a0 : T := ⟨A0, Subring.subset_closure (by simp)⟩
  let a1 : T := ⟨A1, Subring.subset_closure (by simp)⟩
  let a2 : T := ⟨A2, Subring.subset_closure (by simp)⟩
  have c0 : a0 ^ 3 = 1 := Subtype.ext (by simpa using hW.cube0)
  have c1 : a1 ^ 3 = 1 := Subtype.ext (by simpa using hW.cube1)
  have c2 : a2 ^ 3 = 1 := Subtype.ext (by simpa using hW.cube2)
  have k1 : (a0 * a1 ^ 2) ^ 3 = 1 := by linear_combination (a1 ^ 6) * c0 + (a1 ^ 3 + 1) * c1
  have k2 : (a0 * a1 * a2) ^ 3 = 1 := by
    linear_combination (a1 ^ 3 * a2 ^ 3) * c0 + (a2 ^ 3) * c1 + c2
  have k3 : (a0 * a1 ^ 2) * (a0 * a1 * a2) = (a0 * a1 * a2) * (a0 * a1 ^ 2) := by ring
  have k4 : (a0 * a1 ^ 2) * (a0 * a1 * a2) = a0 ^ 2 * a2 := by
    linear_combination (a0 ^ 2 * a2) * c1
  have k5 : (a0 * a1 ^ 2) * (a0 * a1 * a2) ^ 2 = a1 * a2 ^ 2 := by
    linear_combination (a1 ^ 4 * a2 ^ 2) * c0 + (a1 * a2 ^ 2) * c1
  exact ⟨congrArg Subtype.val k1, congrArg Subtype.val k2, congrArg Subtype.val k3,
    congrArg Subtype.val k4, congrArg Subtype.val k5⟩

theorem Wt49.X_comm_z (hW : Wt49 A0 A1 A2 X Xi S Si) :
    X * (A0 * A1 * A2) = (A0 * A1 * A2) * X := by
  have m0 : A0 * X = X * A1 := by
    calc A0 * X = (X * Xi) * A0 * X := by rw [hW.XXi, one_mul]
      _ = X * (Xi * A0 * X) := by simp only [mul_assoc]
      _ = X * A1 := by rw [hW.rot0]
  have m1 : A1 * X = X * A2 := by
    calc A1 * X = (X * Xi) * A1 * X := by rw [hW.XXi, one_mul]
      _ = X * (Xi * A1 * X) := by simp only [mul_assoc]
      _ = X * A2 := by rw [hW.rot1]
  have m2 : A2 * X = X * A0 := by
    calc A2 * X = (X * Xi) * A2 * X := by rw [hW.XXi, one_mul]
      _ = X * (Xi * A2 * X) := by simp only [mul_assoc]
      _ = X * A0 := by rw [hW.rot2]
  have hc : A0 * A1 * A2 = A1 * A2 * A0 := by
    calc A0 * A1 * A2 = A1 * A0 * A2 := by rw [hW.comm01]
      _ = A1 * (A0 * A2) := by rw [mul_assoc]
      _ = A1 * (A2 * A0) := by rw [hW.comm02]
      _ = A1 * A2 * A0 := by rw [mul_assoc]
  calc X * (A0 * A1 * A2) = X * (A1 * A2 * A0) := by rw [← hc]
    _ = (A0 * A1 * A2) * X := by
      calc X * (A1 * A2 * A0) = (X * A1) * A2 * A0 := by simp only [mul_assoc]
        _ = (A0 * X) * A2 * A0 := by rw [m0]
        _ = A0 * (X * A2) * A0 := by simp only [mul_assoc]
        _ = A0 * (A1 * X) * A0 := by rw [m1]
        _ = A0 * A1 * (X * A0) := by simp only [mul_assoc]
        _ = A0 * A1 * (A2 * X) := by rw [m2]
        _ = (A0 * A1 * A2) * X := by simp only [mul_assoc]

theorem Wt49.Xi_b_X (hW : Wt49 A0 A1 A2 X Xi S Si) :
    Xi * (A0 * A1 ^ 2) * X = (A0 * A1 ^ 2) * (A0 * A1 * A2) ^ 2 := by
  have e : (Xi * A0 * X) * (Xi * A1 * X) * (Xi * A1 * X) =
      Xi * A0 * (X * Xi) * A1 * (X * Xi) * A1 * X := by simp only [mul_assoc]
  have h1 : Xi * (A0 * A1 ^ 2) * X = A1 * A2 ^ 2 := by
    have h2 : Xi * (A0 * A1 ^ 2) * X = (Xi * A0 * X) * (Xi * A1 * X) * (Xi * A1 * X) := by
      rw [e, hW.XXi, pow_two]
      simp only [mul_one, mul_assoc]
    rw [h2, hW.rot0, hW.rot1, pow_two, mul_assoc]
  rw [h1, hW.rels.2.2.2.2]

theorem Wt49.card_Uz (hW : Wt49 A0 A1 A2 X Xi S Si) : Nat.card ↥(Uz A0 A1 A2) = 64 := by
  obtain ⟨hB, hZ, hBZ, -, -⟩ := hW.rels
  exact U_card_eq_64 (A0 * A1 ^ 2) (A0 * A1 * A2) X Xi hW.XiX hW.XXi hB hZ hBZ hW.X_comm_z
    hW.Xi_b_X hW.ne_one hW.card_le

theorem Wt49.pieces (hW : Wt49 A0 A1 A2 X Xi S Si) :
    Uz A0 A1 A2 = Wb A0 A1 A2 ⊔ Wbz A0 A1 A2 ⊔ Wbz2 A0 A1 A2 ∧
      Nat.card ↥(Wb A0 A1 A2) = 4 ∧ Nat.card ↥(Wbz A0 A1 A2) = 4 ∧
      Nat.card ↥(Wbz2 A0 A1 A2) = 4 := by
  obtain ⟨hB, hZ, hBZ, -, -⟩ := hW.rels
  obtain ⟨hU, h1, h2, h3, -, -⟩ := U_decomp (A0 * A1 ^ 2) (A0 * A1 * A2) X Xi hW.XiX hW.XXi
    hB hZ hBZ hW.X_comm_z hW.Xi_b_X
  have h64 := hW.card_Uz
  have h3' : Nat.card ↥(Uz A0 A1 A2) =
      Nat.card ↥(Wb A0 A1 A2) * Nat.card ↥(Wbz A0 A1 A2) * Nat.card ↥(Wbz2 A0 A1 A2) := h3
  have h1' : Nat.card ↥(Wb A0 A1 A2) = Nat.card ↥(Wbz A0 A1 A2) := h1
  have h2' : Nat.card ↥(Wb A0 A1 A2) = Nat.card ↥(Wbz2 A0 A1 A2) := h2
  have hc : Nat.card ↥(Wb A0 A1 A2) = 4 := by
    generalize Nat.card ↥(Wb A0 A1 A2) = c at h3' h1' h2' ⊢
    rw [← h1', ← h2'] at h3'
    have hle : c ≤ 4 := by
      by_contra hlt
      push Not at hlt
      nlinarith
    interval_cases c <;> omega
  exact ⟨hU, hc, h1' ▸ hc, h2' ▸ hc⟩

theorem Wt49.exists_ne_zero_Wbz2 (hW : Wt49 A0 A1 A2 X Xi S Si) :
    ∃ w ∈ Wbz2 A0 A1 A2, w ≠ 0 := by
  have hcard := hW.pieces.2.2.2
  have hn : Nontrivial ↥(Wbz2 A0 A1 A2) := by
    rw [← Finite.one_lt_card_iff_nontrivial, hcard]
    norm_num
  obtain ⟨w, hw⟩ := exists_ne (0 : ↥(Wbz2 A0 A1 A2))
  exact ⟨w.1, w.2, fun h => hw (Subtype.ext h)⟩

theorem Wt49.prod_rotate (hW : Wt49 A0 A1 A2 X Xi S Si) : A1 * A2 * A0 = A0 * A1 * A2 := by
  calc A1 * A2 * A0 = A1 * (A2 * A0) := by rw [mul_assoc]
    _ = A1 * (A0 * A2) := by rw [hW.comm02]
    _ = A1 * A0 * A2 := by rw [mul_assoc]
    _ = A0 * A1 * A2 := by rw [hW.comm01]

theorem Wt49.rotate (hW : Wt49 A0 A1 A2 X Xi S Si) :
    Wt49 A1 A2 A0 X Xi (Xi * S * X) (Xi * Si * X) := by
  have hA0 : X * A1 * Xi = A0 := by
    calc X * A1 * Xi = X * (Xi * A0 * X) * Xi := by rw [hW.rot0]
      _ = (X * Xi) * A0 * (X * Xi) := by simp only [mul_assoc]
      _ = A0 := by rw [hW.XXi, one_mul, mul_one]
  have hA1 : X * A2 * Xi = A1 := by
    calc X * A2 * Xi = X * (Xi * A1 * X) * Xi := by rw [hW.rot1]
      _ = (X * Xi) * A1 * (X * Xi) := by simp only [mul_assoc]
      _ = A1 := by rw [hW.XXi, one_mul, mul_one]
  have hA2 : X * A0 * Xi = A2 := by
    calc X * A0 * Xi = X * (Xi * A2 * X) * Xi := by rw [hW.rot2]
      _ = (X * Xi) * A2 * (X * Xi) := by simp only [mul_assoc]
      _ = A2 := by rw [hW.XXi, one_mul, mul_one]
  have hsq : Xi * A0 ^ 2 * X = A1 ^ 2 := by
    have h : (Xi * A0 * X) * (Xi * A0 * X) = Xi * (A0 * A0) * X := by
      calc (Xi * A0 * X) * (Xi * A0 * X) = Xi * A0 * (X * Xi) * A0 * X := by
            simp only [mul_assoc]
        _ = Xi * (A0 * A0) * X := by rw [hW.XXi]; simp only [mul_one, mul_assoc]
    rw [pow_two, ← h, hW.rot0, pow_two]
  refine ⟨hW.cube1, hW.cube2, hW.cube0, hW.comm12, hW.comm01.symm, hW.comm02.symm, hW.XiX,
    hW.XXi, hW.rot1, hW.rot2, hW.rot0, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · calc Xi * Si * X * (Xi * S * X) = Xi * Si * (X * Xi) * S * X := by simp only [mul_assoc]
      _ = Xi * (Si * S) * X := by rw [hW.XXi]; simp only [mul_one, mul_assoc]
      _ = 1 := by rw [hW.SiS, mul_one, hW.XiX]
  · calc Xi * S * X * (Xi * Si * X) = Xi * S * (X * Xi) * Si * X := by simp only [mul_assoc]
      _ = Xi * (S * Si) * X := by rw [hW.XXi]; simp only [mul_one, mul_assoc]
      _ = 1 := by rw [hW.SSi, mul_one, hW.XiX]
  · calc Xi * Si * X * A1 * (Xi * S * X) = Xi * Si * (X * A1 * Xi) * S * X := by
          simp only [mul_assoc]
      _ = Xi * (Si * A0 * S) * X := by rw [hA0]; simp only [mul_assoc]
      _ = A1 ^ 2 := by rw [hW.inv0, hsq]
  · calc Xi * Si * X * A2 * (Xi * S * X) = Xi * Si * (X * A2 * Xi) * S * X := by
          simp only [mul_assoc]
      _ = Xi * (Si * A1 * S) * X := by rw [hA1]; simp only [mul_assoc]
      _ = A2 := by rw [hW.fix1, hW.rot1]
  · calc Xi * Si * X * A0 * (Xi * S * X) = Xi * Si * (X * A0 * Xi) * S * X := by
          simp only [mul_assoc]
      _ = Xi * (Si * A2 * S) * X := by rw [hA2]; simp only [mul_assoc]
      _ = A0 := by rw [hW.fix2, hW.rot2]
  · rw [hW.prod_rotate]; exact hW.ne_one
  · rw [hW.prod_rotate]; exact hW.card_le

theorem Wt49.rot_rels (hW : Wt49 A0 A1 A2 X Xi S Si) :
    A1 * A2 ^ 2 * (A1 * A2 * A0) = A0 * A1 ^ 2 ∧
      A1 * A2 ^ 2 * (A1 * A2 * A0) ^ 2 = A0 * A1 ^ 2 * (A0 * A1 * A2) := by
  let T : Subring (Module.End (ZMod 2) V) := Subring.closure ({A0, A1, A2} : Set _)
  letI : CommRing T := Subring.closureCommRingOfComm
    (pairwise_commute_triple hW.comm01 hW.comm02 hW.comm12)
  let a0 : T := ⟨A0, Subring.subset_closure (by simp)⟩
  let a1 : T := ⟨A1, Subring.subset_closure (by simp)⟩
  let a2 : T := ⟨A2, Subring.subset_closure (by simp)⟩
  have c2 : a2 ^ 3 = 1 := Subtype.ext (by simpa using hW.cube2)
  have k1 : a1 * a2 ^ 2 * (a1 * a2 * a0) = a0 * a1 ^ 2 := by
    linear_combination (a1 ^ 2 * a0) * c2
  have k2 : a1 * a2 ^ 2 * (a1 * a2 * a0) ^ 2 = a0 * a1 ^ 2 * (a0 * a1 * a2) := by
    linear_combination (a1 ^ 3 * a0 ^ 2 * a2) * c2
  exact ⟨congrArg Subtype.val k1, congrArg Subtype.val k2⟩

theorem Wt49.Uz_rotate (hW : Wt49 A0 A1 A2 X Xi S Si) : Uz A1 A2 A0 = Uz A0 A1 A2 := by
  unfold Uz
  rw [hW.prod_rotate]

theorem Wt49.Wb_rotate (hW : Wt49 A0 A1 A2 X Xi S Si) : Wb A1 A2 A0 = Wbz2 A0 A1 A2 := by
  unfold Wb Wbz2
  rw [hW.Uz_rotate, hW.rels.2.2.2.2]

theorem Wt49.Wbz_rotate (hW : Wt49 A0 A1 A2 X Xi S Si) : Wbz A1 A2 A0 = Wb A0 A1 A2 := by
  unfold Wbz Wb
  rw [hW.Uz_rotate, hW.rot_rels.1]

theorem Wt49.Wbz2_rotate (hW : Wt49 A0 A1 A2 X Xi S Si) : Wbz2 A1 A2 A0 = Wbz A0 A1 A2 := by
  unfold Wbz2 Wbz
  rw [hW.Uz_rotate, hW.rot_rels.2]

theorem Wt49.patI_rotate (hW : Wt49 A0 A1 A2 X Xi S Si) (h : PatI A0 A1 A2) :
    PatI A1 A2 A0 := by
  obtain ⟨⟨h00, h01, h02⟩, ⟨h10, h11, h12⟩, ⟨h20, h21, h22⟩⟩ := h
  unfold PatI
  rw [hW.Wb_rotate, hW.Wbz_rotate, hW.Wbz2_rotate]
  exact ⟨⟨h21, h22, h20⟩, ⟨h01, h02, h00⟩, ⟨h11, h12, h10⟩⟩

theorem Wt49.patIIb_rotate (hW : Wt49 A0 A1 A2 X Xi S Si) (h : PatIIb A0 A1 A2) :
    PatIIb A1 A2 A0 := by
  obtain ⟨⟨h00, h01, h02⟩, ⟨h10, h11, h12⟩, ⟨h20, h21, h22⟩⟩ := h
  unfold PatIIb
  rw [hW.Wb_rotate, hW.Wbz_rotate, hW.Wbz2_rotate]
  exact ⟨⟨h21, h22, h20⟩, ⟨h01, h02, h00⟩, ⟨h11, h12, h10⟩⟩

theorem Disj49.rotate (h : Disj49 A0 A1 A2) : Disj49 A1 A2 A0 := by
  obtain ⟨h01, h02, h12⟩ := h
  exact ⟨h12, by rwa [inf_comm], by rwa [inf_comm]⟩

end OperatorLemmas

section Helpers

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

theorem finrank_eq_of_mutual {S Si : Module.End (ZMod 2) V} (hSiS : Si * S = 1)
    (hSSi : S * Si = 1) {P Q : Submodule (ZMod 2) V} (hP : ∀ v ∈ P, S v ∈ Q)
    (hQ : ∀ v ∈ Q, Si v ∈ P) :
    Module.finrank (ZMod 2) ↥P = Module.finrank (ZMod 2) ↥Q := by
  have e : ↥P ≃ₗ[ZMod 2] ↥Q := LinearEquiv.ofLinear (S.restrict hP) (Si.restrict hQ)
    (by
      apply LinearMap.ext
      intro w
      apply Subtype.ext
      change S (Si (w : V)) = (w : V)
      rw [← Module.End.mul_apply, hSSi, Module.End.one_apply])
    (by
      apply LinearMap.ext
      intro v
      apply Subtype.ext
      change Si (S (v : V)) = (v : V)
      rw [← Module.End.mul_apply, hSiS, Module.End.one_apply])
  exact e.finrank_eq

theorem e2_decomp_vec {P Q : Module.End (ZMod 2) V} (hP : P ^ 3 = 1) (hQ : Q ^ 3 = 1)
    (hPQ : P * Q = Q * P) (v : V) :
    v = e2 P v + e2 (P * Q) v + e2 (P * Q ^ 2) v + e2 Q v + e2 P (e2 Q v) := by
  have h := LinearMap.congr_fun (e2_end_sum P Q hP hQ hPQ) v
  simp only [LinearMap.add_apply, Module.End.one_apply, Module.End.mul_apply] at h
  calc v = (v + e2 P (e2 Q v)) + e2 P (e2 Q v) := by
        rw [add_assoc, add_self_eq_zero_zmod2, add_zero]
    _ = _ := by rw [← h]

theorem le_ker_e2_of_fpf {Z : Module.End (ZMod 2) V} (hZ : Z ^ 3 = 1) {D : Submodule (ZMod 2) V}
    (hD : ∀ v ∈ D, Z v ∈ D) (hfpf : ∀ v ∈ D, Z v = v → v = 0) :
    D ≤ LinearMap.ker (e2 Z) := by
  intro v hv
  rw [LinearMap.mem_ker]
  apply hfpf (e2 Z v)
  · rw [e2_eq Z hZ]
    simp only [LinearMap.add_apply, Module.End.one_apply, pow_two, Module.End.mul_apply]
    exact D.add_mem (D.add_mem hv (hD v hv)) (hD _ (hD v hv))
  · exact g_apply_e2 Z hZ v

private theorem base_mul_cube_eq_one {A B : Module.End (ZMod 2) V} (hA : A ^ 3 = 1)
    (hB : B ^ 3 = 1) (hAB : A * B = B * A) :
    (A * B) ^ 3 = 1 ∧ (A * B ^ 2) ^ 3 = 1 := by
  constructor
  · rw [Commute.mul_pow hAB, hA, hB, mul_one]
  · rw [Commute.mul_pow (Commute.pow_right hAB 2) 3, hA, ← pow_mul,
      show 2 * 3 = 3 * 2 by norm_num, pow_mul, hB, one_pow, mul_one]

private theorem base_conj_AB2_eq_sq {A B S Si : Module.End (ZMod 2) V}
    (hAB : A * B = B * A) (hSSi : S * Si = 1) (hSA : Si * A * S = A ^ 2)
    (hSB : Si * B * S = B) :
    Si * (A * B ^ 2) * S = (A * B) ^ 2 := by
  have hB2 : Si * B ^ 2 * S = B ^ 2 := by
    rw [pow_two]
    calc Si * (B * B) * S = Si * B * (S * Si) * B * S := by
          rw [hSSi, mul_one]; simp only [mul_assoc]
      _ = (Si * B * S) * (Si * B * S) := by simp only [mul_assoc]
      _ = B * B := by rw [hSB]
  calc Si * (A * B ^ 2) * S = Si * A * (S * Si) * B ^ 2 * S := by
        rw [hSSi, mul_one]; simp only [mul_assoc]
    _ = (Si * A * S) * (Si * B ^ 2 * S) := by simp only [mul_assoc]
    _ = A ^ 2 * B ^ 2 := by rw [hSA, hB2]
    _ = (A * B) ^ 2 := (Commute.mul_pow hAB 2).symm

private theorem base_AB2_mul_conj {A B S Si : Module.End (ZMod 2) V} (hSSi : S * Si = 1)
    (hconj : Si * (A * B ^ 2) * S = (A * B) ^ 2) :
    (A * B ^ 2) * S = S * (A * B) ^ 2 ∧ Si * (A * B ^ 2) = (A * B) ^ 2 * Si := by
  constructor
  · calc (A * B ^ 2) * S = (S * Si) * (A * B ^ 2) * S := by rw [hSSi, one_mul]
      _ = S * (Si * (A * B ^ 2) * S) := by simp only [mul_assoc]
      _ = S * (A * B) ^ 2 := by rw [hconj]
  · calc Si * (A * B ^ 2) = Si * (A * B ^ 2) * (S * Si) := by rw [hSSi, mul_one]
      _ = (Si * (A * B ^ 2) * S) * Si := by simp only [mul_assoc]
      _ = (A * B) ^ 2 * Si := by rw [hconj]

private theorem base_S_maps_fixed_AB {A B S : Module.End (ZMod 2) V} (hA : A ^ 3 = 1)
    (hB : B ^ 3 = 1) (hAB : A * B = B * A)
    (hg : (A * B ^ 2) * S = S * (A * B) ^ 2) {P : Submodule (ZMod 2) V}
    (hP : ∀ v ∈ P, S v ∈ P) :
    ∀ v ∈ P ⊓ LinearMap.range (e2 (A * B)), S v ∈ P ⊓ LinearMap.range (e2 (A * B ^ 2)) := by
  obtain ⟨hAB3, hg3⟩ := base_mul_cube_eq_one hA hB hAB
  rintro v ⟨hvP, hv⟩
  refine ⟨hP v hvP, (mem_range_e2_iff (A * B ^ 2) hg3 (S v)).mpr ?_⟩
  have hv' : (A * B) v = v := (mem_range_e2_iff (A * B) hAB3 v).mp hv
  have hv2 : ((A * B) ^ 2) v = v := by rw [pow_two, Module.End.mul_apply, hv', hv']
  calc (A * B ^ 2) (S v) = ((A * B ^ 2) * S) v := rfl
    _ = (S * (A * B) ^ 2) v := by rw [hg]
    _ = S (((A * B) ^ 2) v) := rfl
    _ = S v := by rw [hv2]

private theorem base_Si_maps_fixed_AB2 {A B Si : Module.End (ZMod 2) V} (hA : A ^ 3 = 1)
    (hB : B ^ 3 = 1) (hAB : A * B = B * A)
    (hg' : Si * (A * B ^ 2) = (A * B) ^ 2 * Si) {P : Submodule (ZMod 2) V}
    (hP' : ∀ v ∈ P, Si v ∈ P) :
    ∀ v ∈ P ⊓ LinearMap.range (e2 (A * B ^ 2)), Si v ∈ P ⊓ LinearMap.range (e2 (A * B)) := by
  obtain ⟨hAB3, hg3⟩ := base_mul_cube_eq_one hA hB hAB
  rintro w ⟨hwP, hw⟩
  refine ⟨hP' w hwP, (mem_range_e2_iff (A * B) hAB3 (Si w)).mpr ?_⟩
  have hw' : (A * B ^ 2) w = w := (mem_range_e2_iff (A * B ^ 2) hg3 w).mp hw
  have h2 : ((A * B) ^ 2) (Si w) = Si w := by
    calc ((A * B) ^ 2) (Si w) = ((A * B) ^ 2 * Si) w := rfl
      _ = (Si * (A * B ^ 2)) w := by rw [hg']
      _ = Si ((A * B ^ 2) w) := rfl
      _ = Si w := by rw [hw']
  calc (A * B) (Si w) = (A * B) (((A * B) ^ 2) (Si w)) := by rw [h2]
    _ = ((A * B) ^ 3) (Si w) := by rw [pow_succ' (A * B) 2]; rfl
    _ = Si w := by rw [hAB3]; rfl

theorem finrank_inf_conj_eq {A B S Si : Module.End (ZMod 2) V} (hA : A ^ 3 = 1) (hB : B ^ 3 = 1)
    (hAB : A * B = B * A) (hSiS : Si * S = 1) (hSSi : S * Si = 1)
    (hSA : Si * A * S = A ^ 2) (hSB : Si * B * S = B) {P : Submodule (ZMod 2) V}
    (hP : ∀ v ∈ P, S v ∈ P) (hP' : ∀ v ∈ P, Si v ∈ P) :
    Module.finrank (ZMod 2) ↥(P ⊓ LinearMap.range (e2 (A * B))) =
      Module.finrank (ZMod 2) ↥(P ⊓ LinearMap.range (e2 (A * B ^ 2))) := by
  have hconj : Si * (A * B ^ 2) * S = (A * B) ^ 2 := base_conj_AB2_eq_sq hAB hSSi hSA hSB
  obtain ⟨hg, hg'⟩ := base_AB2_mul_conj hSSi hconj
  exact finrank_eq_of_mutual hSiS hSSi (S := S) (Si := Si)
    (base_S_maps_fixed_AB hA hB hAB hg hP)
    (base_Si_maps_fixed_AB2 hA hB hAB hg' hP')

end Helpers

section Context

variable {H X L Q I : Subgroup G} {x : G} {A : Subgroup G} {a n : G} {N M : Subgroup G}

noncomputable abbrev op49 (hch : HChief H N M) [(M.subgroupOf N).Normal]
    [IsElementaryAbelian 2 (N ⧸ M.subgroupOf N)] (g : ↥H) :
    Module.End (ZMod 2) (Additive (N ⧸ M.subgroupOf N)) :=
  (chiefRep (p := 2) hch.2.1 hch.2.2.1 g).val

structure Ctx49 (H X L Q I : Subgroup G) (x : G) (A : Subgroup G) (a n : G)
    (N M : Subgroup G) : Prop where
  setup : Setup49 H X L Q I
  hx : X = Subgroup.zpowers x
  xa : XAData X L I x A a n
  chief : HChief H N M
  NQ : N ≤ Q
  nontriv : ¬ ⁅N, I⁆ ≤ M
  weight : wIdx (Z49 X A) N M ≤ 64

namespace Ctx49

variable (c : Ctx49 H X L Q I x A a n N M)

include c

theorem xX : x ∈ X := c.hx ▸ Subgroup.mem_zpowers x

theorem ord : orderOf x = 3 := orderOf_eq_three_of_zpowers c.hx c.setup.card_X

theorem x3 : x ^ 3 = 1 := by
  rw [← c.ord]
  exact pow_orderOf_eq_one x

theorem pow_mem (i : ℕ) : x ^ i ∈ X := X.pow_mem c.xX i

theorem I_eq : I = Lc L x 0 ⊔ Lc L x 1 ⊔ Lc L x 2 := by
  rw [I_eq_sup_conjugates49 c.setup c.xX c.hx]
  simp only [Lc, pow_zero, pow_one, conjugate_one]

theorem Lc_ne {i j : ℕ} (hi : i < 3) (hj : j < 3) (hij : i ≠ j) : Lc L x i ≠ Lc L x j := by
  obtain ⟨h01, h02, h12⟩ := conjugates_distinct c.setup c.xX c.hx c.ord
  interval_cases i <;> interval_cases j <;>
    first | exact absurd rfl hij | assumption | exact Ne.symm ‹_›

theorem Lc_I (i : ℕ) : Lc L x i ≤ I := conjugate_le_I c.setup (c.pow_mem i)

theorem Lc_H (i : ℕ) : Lc L x i ≤ H := (c.Lc_I i).trans (I_le_H c.setup)

theorem Lc_norm {i j : ℕ} (hi : i < 3) (hj : j < 3) (hij : i ≠ j) :
    Lc L x i ≤ Subgroup.normalizer (Lc L x j : Set G) :=
  conjugate_normalize_of_ne c.setup (c.pow_mem i) (c.pow_mem j) (c.Lc_ne hi hj hij)

theorem Lc_comm {i j : ℕ} (hi : i < 3) (hj : j < 3) (hij : i ≠ j) :
    ⁅Lc L x i, Lc L x j⁆ ≤ Q :=
  commutator_conjugate_le c.setup (c.pow_mem i) (c.pow_mem j) (c.Lc_ne hi hj hij)

theorem Lc_alt (i : ℕ) : IsAlt (Bar2 (Lc L x i)) 5 := isAlt_bar2_conjugate c.setup.L_alt (x ^ i)

theorem Lc_pCore (i : ℕ) :
    (Lc L x i ⊓ Q).subgroupOf (Lc L x i) = CFSG.pCore 2 ↥(Lc L x i) := by
  have hbridge : ∀ K : Subgroup G,
      ((CFSG.pCore 2 ↥K).map K.subtype).subgroupOf K = CFSG.pCore 2 ↥K := by
    intro K
    ext y
    constructor
    · intro hy
      obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.mp (Subgroup.mem_subgroupOf.mp hy)
      rwa [show z = y from Subtype.ext hzy] at hz
    · intro hy
      exact Subgroup.mem_subgroupOf.mpr (Subgroup.mem_map.mpr ⟨y, hy, rfl⟩)
  rw [Lc, conjugate_inf_pCoreOf_eq c.setup (c.pow_mem i), CFSG.Open.pCoreOf]
  exact hbridge _

@[expose] def ai (i : ℕ) : ↥H :=
  ⟨cj (x ^ i) a, c.Lc_H i (conjugate_cj L a (x ^ i) c.xa.a_mem)⟩

@[simp] theorem ai_coe (i : ℕ) : ((c.ai i : ↥H) : G) = cj (x ^ i) a := rfl

theorem ai_mem (i : ℕ) : ((c.ai i : ↥H) : G) ∈ Lc L x i :=
  conjugate_cj L a (x ^ i) c.xa.a_mem

theorem ai_not_mem_Q (i : ℕ) : ((c.ai i : ↥H) : G) ∉ Q := by
  intro hq
  have h3 : orderOf (cj (x ^ i) a) = 3 := by
    have hsem : SemiconjBy (x ^ i)⁻¹ a (cj (x ^ i) a) := by
      simp only [SemiconjBy, cj]
      group
    rw [← SemiconjBy.orderOf_eq (x ^ i)⁻¹ hsem]
    exact c.xa.ord
  have hdvd : orderOf (cj (x ^ i) a) ∣ Nat.card Q := by
    have h1 := orderOf_dvd_natCard (⟨cj (x ^ i) a, hq⟩ : ↥Q)
    rw [← Subgroup.orderOf_coe] at h1
    exact h1
  obtain ⟨k, hk⟩ := (isPGroup_Q c.setup).exists_card_eq
  rw [h3, hk] at hdvd
  exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three hdvd) (by norm_num)

@[expose] def xH : ↥H := ⟨x, c.setup.X_le c.xX⟩

@[expose] def nH : ↥H := ⟨n, I_le_H c.setup c.xa.n_mem⟩

variable [hNorm : (M.subgroupOf N).Normal] [hElem : IsElementaryAbelian 2 (N ⧸ M.subgroupOf N)]

noncomputable abbrev opA (i : ℕ) : Module.End (ZMod 2) (Additive (N ⧸ M.subgroupOf N)) :=
  op49 c.chief (c.ai i)

noncomputable abbrev opX : Module.End (ZMod 2) (Additive (N ⧸ M.subgroupOf N)) :=
  op49 c.chief c.xH

noncomputable abbrev opXi : Module.End (ZMod 2) (Additive (N ⧸ M.subgroupOf N)) :=
  op49 c.chief c.xH⁻¹

noncomputable abbrev opS : Module.End (ZMod 2) (Additive (N ⧸ M.subgroupOf N)) :=
  op49 c.chief c.nH

noncomputable abbrev opSi : Module.End (ZMod 2) (Additive (N ⧸ M.subgroupOf N)) :=
  op49 c.chief c.nH⁻¹

theorem op_comm {i j : ℕ} (hi : i < 3) (hj : j < 3) (hij : i ≠ j) {g g' : ↥H}
    (hg : (g : G) ∈ Lc L x i) (hg' : (g' : G) ∈ Lc L x j) :
    op49 c.chief g * op49 c.chief g' = op49 c.chief g' * op49 c.chief g :=
  chief_struct49_rho_commute_of_Q c.setup c.chief c.NQ
    ((Subgroup.commutator_le.mp (c.Lc_comm hi hj hij)) (g : G) hg (g' : G) hg')

theorem Lc_trivial_of_invariant (k : ℕ)
    (W : Submodule (ZMod 2) (Additive (N ⧸ M.subgroupOf N)))
    (hW : ∀ g : ↥H, (g : G) ∈ Lc L x k → ∀ w ∈ W, op49 c.chief g w ∈ W)
    (hfix : ∀ w ∈ W, op49 c.chief (c.ai k) w = w) :
    ∀ g : ↥H, (g : G) ∈ Lc L x k → ∀ w ∈ W, op49 c.chief g w = w :=
  chief_struct49_Lk_trivial_of_invariant c.setup c.chief c.NQ (c.Lc_H k) (c.ai_mem k)
    (c.Lc_alt k) (c.Lc_pCore k) (c.ai_not_mem_Q k) W hW hfix

theorem eq_zero_of_fixed {v : Additive (N ⧸ M.subgroupOf N)}
    (h0 : ∀ g : ↥H, (g : G) ∈ Lc L x 0 → op49 c.chief g v = v)
    (h1 : ∀ g : ↥H, (g : G) ∈ Lc L x 1 → op49 c.chief g v = v)
    (h2 : ∀ g : ↥H, (g : G) ∈ Lc L x 2 → op49 c.chief g v = v) : v = 0 := by
  have hmem : v ∈ CV_I c.setup c.chief := by
    intro g
    have hgI : (g : G) ∈ Lc L x 0 ⊔ Lc L x 1 ⊔ Lc L x 2 := by
      rw [← c.I_eq]
      exact g.2
    have hN2 : Lc L x 0 ⊔ Lc L x 1 ≤ Subgroup.normalizer (Lc L x 2 : Set G) :=
      sup_le (c.Lc_norm (by norm_num) (by norm_num) (by norm_num))
        (c.Lc_norm (by norm_num) (by norm_num) (by norm_num))
    have hN1 : Lc L x 0 ≤ Subgroup.normalizer (Lc L x 1 : Set G) :=
      c.Lc_norm (by norm_num) (by norm_num) (by norm_num)
    obtain ⟨m, hm, l2, hl2, hm_eq⟩ := (mem_sup_of_le_normalizer (x := (g : G)) hN2).mp hgI
    obtain ⟨l0, hl0, l1, hl1, hl0_eq⟩ := (mem_sup_of_le_normalizer (x := m) hN1).mp hm
    have hg_eq : (g : G) = (l0 * l1) * l2 := by rw [← hm_eq, ← hl0_eq]
    have hlincl : Subgroup.inclusion (I_le_H c.setup) g =
        (⟨l0, c.Lc_H 0 hl0⟩ : ↥H) * (⟨l1, c.Lc_H 1 hl1⟩ : ↥H) * (⟨l2, c.Lc_H 2 hl2⟩ : ↥H) := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inclusion, hg_eq]
    change (chiefRep (p := 2) c.chief.2.1 c.chief.2.2.1
      (Subgroup.inclusion (I_le_H c.setup) g)).val v = v
    rw [hlincl, map_mul, map_mul, Units.val_mul, Units.val_mul, Module.End.mul_apply,
      Module.End.mul_apply]
    exact (congrArg _ (congrArg _ (h2 ⟨l2, c.Lc_H 2 hl2⟩ hl2))).trans
      ((congrArg _ (h1 ⟨l1, c.Lc_H 1 hl1⟩ hl1)).trans (h0 ⟨l0, c.Lc_H 0 hl0⟩ hl0))
  rw [CV_I_eq_bot c.setup c.chief c.nontriv] at hmem
  exact (Submodule.mem_bot _).mp hmem

theorem wt_op_mul (g h : ↥H) :
    op49 c.chief (g * h) = op49 c.chief g * op49 c.chief h := by
  simp [op49]

theorem wt_op_one : op49 c.chief (1 : ↥H) = 1 := by
  simp [op49]

theorem wt_op_pow (g : ↥H) (k : ℕ) :
    op49 c.chief (g ^ k) = op49 c.chief g ^ k := by
  simp [op49]

theorem wt_op_conj {g u w : ↥H} (h : g⁻¹ * u * g = w) :
    op49 c.chief g⁻¹ * op49 c.chief u * op49 c.chief g = op49 c.chief w := by
  simpa [op49] using congrArg (op49 c.chief) h

theorem wt_ai_cube (i : ℕ) : c.ai i ^ 3 = 1 := by
  apply Subtype.ext
  rw [Subgroup.coe_pow, Subgroup.coe_one, c.ai_coe, ← cj_pow, ← c.xa.ord,
    pow_orderOf_eq_one]
  simp [cj]

theorem wt_ai_rot (i : ℕ) : c.xH⁻¹ * c.ai i * c.xH = c.ai (i + 1) := by
  apply Subtype.ext
  show cj x (cj (x ^ i) a) = cj (x ^ (i + 1)) a
  rw [cj_mul, ← pow_succ]

theorem wt_ai_three : c.ai 3 = c.ai 0 := by
  apply Subtype.ext
  simp only [c.ai_coe]
  rw [c.x3, pow_zero]

theorem wt_a_mem_A : a ∈ A := by
  rw [c.xa.gen]
  exact Subgroup.subset_closure (by simp)

theorem wt_a1_mem_A : cj x a ∈ A := by
  rw [c.xa.gen]
  exact Subgroup.subset_closure (by simp)

theorem wt_a2_mem_A : cj (x ^ 2) a ∈ A := by
  rw [c.xa.gen]
  exact Subgroup.subset_closure (by simp)

theorem wt_nai_inv : c.nH⁻¹ * c.ai 0 * c.nH = c.ai 0 ^ 2 := by
  apply Subtype.ext
  show cj n (cj (x ^ 0) a) = (cj (x ^ 0) a) ^ 2
  rw [pow_zero, show cj (1 : G) a = a by simp [cj], c.xa.inv_a,
    inv_eq_iff_mul_eq_one]
  calc a * a ^ 2 = a ^ 3 := by group
    _ = 1 := by rw [← c.xa.ord]; exact pow_orderOf_eq_one a

theorem wt_nai_fix1 : c.nH⁻¹ * c.ai 1 * c.nH = c.ai 1 := by
  apply Subtype.ext
  show cj n (cj (x ^ 1) a) = cj (x ^ 1) a
  rw [pow_one]
  exact c.xa.fix_b

theorem wt_nai_fix2 : c.nH⁻¹ * c.ai 2 * c.nH = c.ai 2 := by
  apply Subtype.ext
  show cj n (cj (x ^ 2) a) = cj (x ^ 2) a
  exact c.xa.fix_c

def wt_z : ↥H := c.ai 0 * c.ai 1 * c.ai 2

theorem wt_z_coe : (wt_z c : G) = a * cj x a * cj (x ^ 2) a := by
  show ((c.ai 0 * c.ai 1 * c.ai 2 : ↥H) : G) = a * cj x a * cj (x ^ 2) a
  simp only [Subgroup.coe_mul, c.ai_coe, pow_zero, pow_one]
  simp [cj]

theorem wt_z_comm : x * (wt_z c : G) = (wt_z c : G) * x := by
  rw [wt_z_coe]
  exact (chief_w49_relations c.setup c.hx c.xa).2.2.2.1

theorem wt_z_mem_Z49 : (wt_z c : G) ∈ Z49 X A := by
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · rw [wt_z_coe]
    exact A.mul_mem (A.mul_mem (wt_a_mem_A c) (wt_a1_mem_A c)) (wt_a2_mem_A c)
  · rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [c.hx] at hy
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact (Commute.zpow_left (wt_z_comm c) m).eq

theorem wt_rho_z_ne_one :
    chiefRep (p := 2) c.chief.2.1 c.chief.2.2.1 (wt_z c) ≠ 1 := by
  intro hrho
  have hz3 : (wt_z c : G) ^ 3 = 1 := by
    rw [wt_z_coe]
    exact (chief_w49_relations c.setup c.hx c.xa).2.2.1
  have hz_ne : (wt_z c : G) ≠ 1 := by
    rw [wt_z_coe]
    exact (chief_w49_relations c.setup c.hx c.xa).2.2.2.2.2
  have htriv : ∀ nn ∈ N, ⁅nn, (wt_z c : G)⁆ ∈ M :=
    fun nn hn => (chiefRep_eq_one_iff (p := 2) c.chief.2.1 c.chief.2.2.1 (wt_z c)).mp
      hrho nn hn
  have hzI : (wt_z c : G) ∈ I := c.xa.A_le (by
    rw [wt_z_coe]
    exact A.mul_mem (A.mul_mem (wt_a_mem_A c) (wt_a1_mem_A c)) (wt_a2_mem_A c))
  have hzQ : (wt_z c : G) ∈ Q :=
    (chief_faithful49 c.setup c.chief c.NQ c.nontriv).2 (wt_z c : G) hzI htriv
  obtain ⟨k, hk⟩ := (isPGroup_Q c.setup).exists_card_eq
  let zQ : ↥Q := ⟨(wt_z c : G), hzQ⟩
  have hdvd : orderOf zQ ∣ 2 ^ k := by
    rw [← hk]
    exact orderOf_dvd_natCard zQ
  have hordz : orderOf zQ = 3 := by
    apply orderOf_eq_prime
    · exact Subtype.ext hz3
    · intro h1
      exact hz_ne (Subtype.ext_iff.mp h1)
  rw [hordz] at hdvd
  have h32 : 3 ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three hdvd
  norm_num at h32

theorem wt : Wt49 (c.opA 0) (c.opA 1) (c.opA 2) c.opX c.opXi c.opS c.opSi :=
  { cube0 := by
      simpa [op49] using congrArg (op49 c.chief) (wt_ai_cube c 0)
    cube1 := by
      simpa [op49] using congrArg (op49 c.chief) (wt_ai_cube c 1)
    cube2 := by
      simpa [op49] using congrArg (op49 c.chief) (wt_ai_cube c 2)
    comm01 := c.op_comm (i := 0) (j := 1) (by norm_num) (by norm_num) (by norm_num)
      (c.ai_mem 0) (c.ai_mem 1)
    comm02 := c.op_comm (i := 0) (j := 2) (by norm_num) (by norm_num) (by norm_num)
      (c.ai_mem 0) (c.ai_mem 2)
    comm12 := c.op_comm (i := 1) (j := 2) (by norm_num) (by norm_num) (by norm_num)
      (c.ai_mem 1) (c.ai_mem 2)
    XiX := by
      show op49 c.chief c.xH⁻¹ * op49 c.chief c.xH = 1
      rw [← wt_op_mul c, inv_mul_cancel, wt_op_one c]
    XXi := by
      show op49 c.chief c.xH * op49 c.chief c.xH⁻¹ = 1
      rw [← wt_op_mul c, mul_inv_cancel, wt_op_one c]
    rot0 := wt_op_conj c (wt_ai_rot c 0)
    rot1 := wt_op_conj c (wt_ai_rot c 1)
    rot2 := by
      have h := wt_ai_rot c 2
      rw [wt_ai_three c] at h
      exact wt_op_conj c h
    SiS := by
      show op49 c.chief c.nH⁻¹ * op49 c.chief c.nH = 1
      rw [← wt_op_mul c, inv_mul_cancel, wt_op_one c]
    SSi := by
      show op49 c.chief c.nH * op49 c.chief c.nH⁻¹ = 1
      rw [← wt_op_mul c, mul_inv_cancel, wt_op_one c]
    inv0 := by
      have h := wt_op_conj c (wt_nai_inv c)
      rwa [wt_op_pow c] at h
    fix1 := wt_op_conj c (wt_nai_fix1 c)
    fix2 := wt_op_conj c (wt_nai_fix2 c)
    ne_one := by
      intro h
      have hz1 : op49 c.chief (c.ai 0 * c.ai 1 * c.ai 2) = 1 := by
        rw [wt_op_mul c, wt_op_mul c]
        exact h
      exact wt_rho_z_ne_one c (Units.val_eq_one.mp hz1)
    card_le := by
      have hfix : op49 c.chief (wt_z c) = c.opA 0 * c.opA 1 * c.opA 2 := by
        show op49 c.chief (c.ai 0 * c.ai 1 * c.ai 2) =
          c.opA 0 * c.opA 1 * c.opA 2
        rw [wt_op_mul c, wt_op_mul c]
      have hcard := chief_card_le_card_fixed_mul_wIdx (hch := c.chief) (Z := Z49 X A)
        (z := wt_z c) (wt_z_mem_Z49 c)
      calc Nat.card (Additive (N ⧸ M.subgroupOf N))
          ≤ Nat.card {v : Additive (N ⧸ M.subgroupOf N) //
              (op49 c.chief (wt_z c)) v = v} * wIdx (Z49 X A) N M := hcard
        _ ≤ Nat.card {v : Additive (N ⧸ M.subgroupOf N) //
              (op49 c.chief (wt_z c)) v = v} * 64 := Nat.mul_le_mul_left _ c.weight
        _ = 64 * Nat.card {v : Additive (N ⧸ M.subgroupOf N) //
              (op49 c.chief (wt_z c)) v = v} := mul_comm _ _
        _ = 64 * Nat.card {v : Additive (N ⧸ M.subgroupOf N) //
              (c.opA 0 * c.opA 1 * c.opA 2) v = v} := by rw [hfix] }

end Ctx49

end Context

end CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC49
