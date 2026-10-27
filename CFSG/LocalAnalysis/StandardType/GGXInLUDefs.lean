module

public import CFSG.LocalAnalysis.StandardType.GGXInLSCLift
public import CFSG.LocalAnalysis.StandardType.GGXInLTransfer
public import CFSG.LocalAnalysis.StandardType.GGXInLQuot
public import CFSG.LocalAnalysis.StandardType.GGXInLCoxSplit
public import CFSG.LocalAnalysis.StandardType.GGQTwoDefs
public import CFSG.Sporadic.Schreier.J4SOrder

public section

open scoped Pointwise

attribute [local instance] commutatorElement

namespace CFSG.StandardType.GGXInL

open CFSG.Assembly

variable {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
  {L D J : Subgroup G} {n : ℕ} {K : Type} [Field K] [Finite K]

structure lup8f_UnitaryMarking (Bs L : Subgroup G) (n : ℕ) (K : Type) [Field K] [Finite K] where
  theta : (↥L) ⧸ Subgroup.center (↥L) ≃* LargeEvenProj (LargeEvenSUGroup (Fin n) K 2)
  card_K : Nat.card K = 4
  normalizes : Bs ≤ Subgroup.normalizer (L : Set G)
  action : ∀ b ∈ Bs, ∃ φ ∈ LargeEvenMatConjImage
      (LargeEvenProjMk (LargeEvenSUGroup (Fin n) K 2)) (LargeEvenGUSet (Fin n) K 2),
    LargeEvenInduces theta (fun l l' => (l' : G) = b⁻¹ * l * b) φ

abbrev lup8f_HT (L Bs : Subgroup G) : Type := ↥(L ⊔ Bs)

abbrev lup8f_L' (L Bs : Subgroup G) : Subgroup (lup8f_HT L Bs) := L.subgroupOf (L ⊔ Bs)

abbrev lup8f_E' (L Bs : Subgroup G) : Subgroup (lup8f_HT L Bs) := Bs.subgroupOf (L ⊔ Bs)

structure lup8f_CentralCover (H : Type) [Group H] (L' E' : Subgroup H) where
  N : Subgroup H
  normal : N.Normal
  le_L : N ≤ L'
  central : ∀ n ∈ N, ∀ l ∈ L', l * n = n * l
  two_group : IsPGroup 2 N
  contains_two : ∀ z ∈ L', (∀ l ∈ L', l * z = z * l) → IsPGroup 2 (Subgroup.zpowers z) → z ∈ N
  coprime : Nat.Coprime 3 (Nat.card N)
  E'_le_norm : E' ≤ Subgroup.normalizer (L' : Set H)

abbrev lup8f_PGU (n : ℕ) (K : Type) [Field K] : Type :=
  LargeEvenProj (Subgroup.closure (LargeEvenGUSet (Fin n) K 2))

@[expose] def lup8f_conjLQ {H : Type} [Group H] (N : Subgroup H) [N.Normal] (L' E' : Subgroup H)
    (h : E' ≤ Subgroup.normalizer (L' : Set H)) (b : ↥E') (l : ↥L') :
    ↥(L'.map (QuotientGroup.mk' N)) :=
  ⟨QuotientGroup.mk' N ((b : H) * (l : H) * (b : H)⁻¹),
    Subgroup.mem_map_of_mem _ ((Subgroup.mem_normalizer_iff.mp (h b.2) (l : H)).mp l.2)⟩

structure lup8f_UFrame0 (H : Type) [Group H] (N : Subgroup H) [N.Normal] (L' E' : Subgroup H)
    (n : ℕ) (K : Type) [Field K] [Finite K] where
  le_L : N ≤ L'
  central : ∀ n ∈ N, ∀ l ∈ L', l * n = n * l
  E'_le_norm : E' ≤ Subgroup.normalizer (L' : Set H)
  eps : ↥(L'.map (QuotientGroup.mk' N)) ≃* ↥(LargeEvenSUGroup (Fin n) K 2)
  mat : ↥E' → GL (Fin n) K
  mat_mem : ∀ b, mat b ∈ LargeEvenGUSet (Fin n) K 2
  mat_ind : ∀ (b : ↥E') (l : ↥L'),
    (eps (lup8f_conjLQ N L' E' E'_le_norm b l) : GL (Fin n) K) =
      MulAut.conj (mat b)
        (eps ⟨QuotientGroup.mk' N (l : H), Subgroup.mem_map_of_mem _ l.2⟩ : GL (Fin n) K)

structure lup8f_UFrame1 (H : Type) [Group H] (N : Subgroup H) [N.Normal] (L' E' : Subgroup H)
    (n : ℕ) (K : Type) [Field K] [Finite K] extends lup8f_UFrame0 H N L' E' n K where
  A : Subgroup (lup8f_PGU n K)
  A_def : A = Subgroup.closure (Set.range fun b : ↥E' =>
      LargeEvenProjMk (Subgroup.closure (LargeEvenGUSet (Fin n) K 2))
        ⟨mat b, Subgroup.subset_closure (mat_mem b)⟩)
  rank_ge : 3 ^ max (n - 3) 3 ≤ Nat.card A

structure lup8f_UFrame2 (H : Type) [Group H] (N : Subgroup H) [N.Normal] (L' E' : Subgroup H)
    (n : ℕ) (K : Type) [Field K] [Finite K] extends lup8f_UFrame1 H N L' E' n K where
  commute : ∀ b b' : ↥E', mat b * mat b' = mat b' * mat b

structure lup8f_UFrame3 (H : Type) [Group H] (N : Subgroup H) [N.Normal] (L' E' : Subgroup H)
    (n : ℕ) (K : Type) [Field K] [Finite K] extends lup8f_UFrame2 H N L' E' n K where
  P : GL (Fin n) K
  P_mem : P ∈ LargeEvenGUSet (Fin n) K 2
  diag : ∀ b : ↥E', ∃ σ : Fin n → Kˣ,
    ((P⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * (mat b : Matrix (Fin n) (Fin n) K) *
      (P : Matrix (Fin n) (Fin n) K) = Matrix.diagonal (fun i => (σ i : K))

@[expose] def lup8f_EpsOver (M : lup8f_UnitaryMarking Bs L n K) (N : Subgroup (lup8f_HT L Bs)) [N.Normal]
    (eps : ↥((lup8f_L' L Bs).map (QuotientGroup.mk' N)) ≃* ↥(LargeEvenSUGroup (Fin n) K 2)) :
    Prop :=
  ∀ l : ↥(lup8f_L' L Bs),
    LargeEvenProjMk (LargeEvenSUGroup (Fin n) K 2)
        (eps ⟨QuotientGroup.mk' N (l : lup8f_HT L Bs), Subgroup.mem_map_of_mem _ l.2⟩) =
      M.theta (QuotientGroup.mk ⟨((l : lup8f_HT L Bs) : G), Subgroup.mem_subgroupOf.mp l.2⟩)

theorem lup8f_L_perfect (hS : GGQTwoSetting p B Bs x L D J) : commutator ↥L = ⊤ :=
  hS.1.2.2.1.1.1

@[expose] def lup8f_diagGL (n : ℕ) (K : Type) [Field K] : (Fin n → Kˣ) →* GL (Fin n) K where
  toFun σ := ⟨Matrix.diagonal (fun i => (σ i : K)), Matrix.diagonal (fun i => ((σ i)⁻¹ : Kˣ)),
    by rw [Matrix.diagonal_mul_diagonal]; simp, by rw [Matrix.diagonal_mul_diagonal]; simp⟩
  map_one' := by ext1; simp
  map_mul' σ τ := by ext1; simp [Matrix.diagonal_mul_diagonal]

@[expose] def lup8f_prodOne (n : ℕ) (K : Type) [Field K] : Subgroup (Fin n → Kˣ) where
  carrier := {σ | ∏ i, σ i = 1}
  mul_mem' := by
    intro σ τ hσ hτ
    simp only [Set.mem_ofPred_eq, Pi.mul_apply, Finset.prod_mul_distrib] at *
    rw [hσ, hτ, one_mul]
  one_mem' := by simp
  inv_mem' := by
    intro σ hσ
    simp only [Set.mem_ofPred_eq, Pi.inv_apply, Finset.prod_inv_distrib] at *
    rw [hσ, inv_one]

@[expose] def lup8f_frameTorusGL (n : ℕ) (K : Type) [Field K] (P : GL (Fin n) K) :
    Subgroup (GL (Fin n) K) :=
  Subgroup.map (MulAut.conj P).toMonoidHom
    (Subgroup.map (lup8f_diagGL n K) (lup8f_prodOne n K))

@[expose] def lup8f_frameT {H : Type} [Group H] {N : Subgroup H} [N.Normal] {L' E' : Subgroup H}
    {n : ℕ} {K : Type} [Field K] [Finite K]
    (F : lup8f_UFrame3 H N L' E' n K) : Subgroup (H ⧸ N) :=
  (((lup8f_frameTorusGL n K F.P).subgroupOf (LargeEvenSUGroup (Fin n) K 2)).comap
    F.eps.toMonoidHom).map (L'.map (QuotientGroup.mk' N)).subtype

structure lup8f_TorusData (S : Type) [Group S] (E0 L0 T : Subgroup S) (z : S) : Prop where
  T_le_E0 : T ≤ E0
  T_le_L0 : T ≤ L0
  T_odd : ∀ t ∈ T, Odd (orderOf t)
  z_mem_L0 : z ∈ L0
  z_center : ∀ l ∈ L0, l * z = z * l
  z_mem_T : z ∈ T
  z_order : orderOf z = 3
  L0_perfect : commutator ↥L0 = ⊤

structure lup8f_CoxeterData (S : Type) [Group S] (E0 L0 T Nsub : Subgroup S) : Prop where
  T_le_Nsub : T ≤ Nsub
  Nsub_le_L0 : Nsub ≤ L0
  Nsub_le_norm : Nsub ≤ Subgroup.normalizer (E0 : Set S)
  T_normal : (T.subgroupOf Nsub).Normal
  coxeter : ∃ (ι : Type) (M : CoxeterMatrix ι),
    Nonempty (CoxeterSystem M (Nsub ⧸ T.subgroupOf Nsub))
  idx : ¬ 3 ∣ Nsub.relIndex L0

structure lup8f_QuotFrame (S : Type) [Group S] (E0 L0 T Nsub : Subgroup S) (z : S) : Prop where
  T_le_E0 : T ≤ E0
  T_odd : ∀ t ∈ T, Odd (orderOf t)
  z_mem_L0 : z ∈ L0
  z_center : ∀ l ∈ L0, l * z = z * l
  z_mem_T : z ∈ T
  z_order : orderOf z = 3
  L0_perfect : commutator ↥L0 = ⊤
  T_le_Nsub : T ≤ Nsub
  Nsub_le_L0 : Nsub ≤ L0
  Nsub_le_norm : Nsub ≤ Subgroup.normalizer (E0 : Set S)
  T_normal : (T.subgroupOf Nsub).Normal
  coxeter : ∃ (ι : Type) (M : CoxeterMatrix ι),
    Nonempty (CoxeterSystem M (Nsub ⧸ T.subgroupOf Nsub))
  idx : ¬ 3 ∣ Nsub.relIndex L0

theorem lup8f_mem_commutator_sup {G : Type} [Group G] {B L : Subgroup G} {x : G} (hxL : x ∈ L) :
    x ∈ ⁅B, L ⊓ Subgroup.normalizer (B : Set G)⁆ ↔
      (⟨x, Subgroup.mem_sup_left hxL⟩ : ↥(L ⊔ B)) ∈
        ⁅B.subgroupOf (L ⊔ B), L.subgroupOf (L ⊔ B) ⊓
          Subgroup.normalizer (B.subgroupOf (L ⊔ B) : Set ↥(L ⊔ B))⁆ := by
  have hK₂ : (L ⊓ Subgroup.normalizer (B : Set G)).subgroupOf (L ⊔ B) =
      L.subgroupOf (L ⊔ B) ⊓
        Subgroup.normalizer (B.subgroupOf (L ⊔ B) : Set ↥(L ⊔ B)) := by
    change (L ⊓ Subgroup.normalizer (B : Set G)).comap (L ⊔ B).subtype =
      L.subgroupOf (L ⊔ B) ⊓
        Subgroup.normalizer (B.subgroupOf (L ⊔ B) : Set ↥(L ⊔ B))
    rw [Subgroup.comap_inf]
    rw [show (Subgroup.normalizer (B : Set G)).comap (L ⊔ B).subtype =
        Subgroup.normalizer (B.subgroupOf (L ⊔ B) : Set ↥(L ⊔ B)) from
      Subgroup.subgroupOf_normalizer_eq le_sup_right]
    rfl
  have hmap : (⁅B.subgroupOf (L ⊔ B),
        (L ⊓ Subgroup.normalizer (B : Set G)).subgroupOf (L ⊔ B)⁆).map (L ⊔ B).subtype =
      ⁅B, L ⊓ Subgroup.normalizer (B : Set G)⁆ := by
    rw [Subgroup.map_commutator]
    congr 1
    · exact Subgroup.map_subgroupOf_eq_of_le le_sup_right
    · exact Subgroup.map_subgroupOf_eq_of_le (le_trans inf_le_left le_sup_left)
  rw [← hK₂]
  constructor
  · intro h
    have h' : x ∈ (⁅B.subgroupOf (L ⊔ B),
        (L ⊓ Subgroup.normalizer (B : Set G)).subgroupOf (L ⊔ B)⁆).map
            (L ⊔ B).subtype := by
      rw [hmap]; exact h
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp h'
    have hyx' : y = ⟨x, Subgroup.mem_sup_left hxL⟩ := Subtype.ext hyx
    rwa [hyx'] at hy
  · intro h
    have h' : x ∈ (⁅B.subgroupOf (L ⊔ B),
        (L ⊓ Subgroup.normalizer (B : Set G)).subgroupOf (L ⊔ B)⁆).map (L ⊔ B).subtype :=
      Subgroup.mem_map_of_mem (L ⊔ B).subtype h
    rwa [hmap] at h'

theorem lup8f_frame_pack {S : Type} [Group S] {E0 L0 T Nsub : Subgroup S} {z : S}
    (hT : lup8f_TorusData S E0 L0 T z) (hC : lup8f_CoxeterData S E0 L0 T Nsub) :
    lup8f_QuotFrame S E0 L0 T Nsub z where
  T_le_E0 := hT.T_le_E0
  T_odd := hT.T_odd
  z_mem_L0 := hT.z_mem_L0
  z_center := hT.z_center
  z_mem_T := hT.z_mem_T
  z_order := hT.z_order
  L0_perfect := hT.L0_perfect
  T_le_Nsub := hC.T_le_Nsub
  Nsub_le_L0 := hC.Nsub_le_L0
  Nsub_le_norm := hC.Nsub_le_norm
  T_normal := hC.T_normal
  coxeter := hC.coxeter
  idx := hC.idx

theorem lup8f_commutator_of_frame {S : Type} [Group S] [Finite S] {E0 L0 T Nsub : Subgroup S}
    {z : S} (hF : lup8f_QuotFrame S E0 L0 T Nsub z) :
    z ∈ ⁅E0, L0 ⊓ Subgroup.normalizer (E0 : Set S)⁆ := by
  classical
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have : (T.subgroupOf Nsub).Normal := hF.T_normal
  have hzNsub : z ∈ Nsub := hF.T_le_Nsub hF.z_mem_T
  let z' : ↥L0 := ⟨z, hF.z_mem_L0⟩
  have hz'c : z' ∈ Subgroup.center ↥L0 := by
    rw [Subgroup.mem_center_iff]
    intro l
    exact Subtype.ext (hF.z_center l l.2)
  have hz'N : z' ∈ Nsub.subgroupOf L0 := Subgroup.mem_subgroupOf.mpr hzNsub
  have hzp : IsPGroup 3 (Subgroup.zpowers z') := by
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_zpowers, pow_one, ← Subgroup.orderOf_coe z']
    exact hF.z_order
  have hzN' : z' ∈ ⁅Nsub.subgroupOf L0, Nsub.subgroupOf L0⁆ :=
    mem_commutator_of_central_of_perfect hF.L0_perfect (Nsub.subgroupOf L0) hF.idx hz'c hz'N hzp
  have hzNN : z ∈ ⁅Nsub, Nsub⁆ := by
    have h := Subgroup.mem_map_of_mem L0.subtype hzN'
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hF.Nsub_le_L0] at h
    simpa [z'] using h
  have hzTNN : z ∈ T ⊓ ⁅Nsub, Nsub⁆ := ⟨hF.z_mem_T, hzNN⟩
  obtain ⟨ι, M, hcs⟩ := hF.coxeter
  obtain ⟨cs⟩ := hcs
  rw [inf_commutator_eq_commutator_of_coxeter_quotient (L := S) Nsub T hF.T_le_Nsub cs
    hF.T_odd] at hzTNN
  exact Subgroup.commutator_mono hF.T_le_E0 (le_inf hF.Nsub_le_L0 hF.Nsub_le_norm) hzTNN


end CFSG.StandardType.GGXInL

end
