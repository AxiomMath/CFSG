module

public import CFSG.LocalAnalysis.SteinbergSFSingleCommFieldFusionDefs
public import CFSG.LocalAnalysis.SteinbergSFSingleCommFieldFusionFrob
public import CFSG.LocalAnalysis.SteinbergSFSingleCommLocalSixHGeneric
public import CFSG.LocalAnalysis.SteinbergSFFullCenterRootNormalizersOrbit
public import CFSG.LocalAnalysis.SteinbergSFFullCenterTorusComplementBase
public import CFSG.LocalAnalysis.SteinbergSFSingleCommNextTwoCoresComplement
public import CFSG.LocalAnalysis.SteinbergSFSingleCommLocalSixFNontrivial
public import CFSG.LocalAnalysis.SteinbergSFSingleCommSquareFactorsBase
public import CFSG.LocalAnalysis.SteinbergSFCentralInvolutionFusion
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Reduce
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19Defs
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_2

public section

namespace CFSG.LocalAnalysis.SymplecticFourStandard

namespace SingleCommParts

open Subgroup GomiFusion
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.QuasithinUnique.Setup.X7b
  CFSG.RankThree.PartOne.KCRootAxis

section Steps

theorem sixFF_ff7_aux_ea_of_sq {H : Type} [Group H] (h : ∀ x : H, x * x = 1) :
    IsElementaryAbelian 2 H := by
  have hcomm : ∀ a b : H, a * b = b * a := by
    intro a b
    have hab := inv_eq_of_mul_eq_one_right (h (a * b))
    rw [mul_inv_rev, inv_eq_of_mul_eq_one_right (h a),
      inv_eq_of_mul_eq_one_right (h b)] at hab
    exact hab.symm
  have hsq : ∀ x : H, x ^ 2 = 1 := fun x => by rw [pow_two]; exact h x
  exact { is_comm := ⟨hcomm⟩, exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one hsq }

theorem sixFF_ff7_aux_quot_ea {G : Type} [Group G] {X Y : Subgroup G}
    [(X.subgroupOf Y).Normal] (hsq : ∀ y : Y, (y : G) * (y : G) ∈ X) :
    IsElementaryAbelian 2 (↥Y ⧸ X.subgroupOf Y) := by
  apply sixFF_ff7_aux_ea_of_sq
  intro q
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
  rw [← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  exact hsq y

theorem sixFF_ff7_aux_sq_mem {G : Type} [Group G] {T N : Subgroup G}
    [(N.subgroupOf T).Normal] (Q : Subgroup (↥T ⧸ N.subgroupOf T))
    (hQ : IsElementaryAbelian 2 ↥Q) (y : T)
    (hy : (QuotientGroup.mk y : ↥T ⧸ N.subgroupOf T) ∈ Q) : (y : G) * (y : G) ∈ N := by
  have h1 : (QuotientGroup.mk y : ↥T ⧸ N.subgroupOf T) ^ 2 = 1 := by
    haveI := hQ
    exact CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := Q) _ hy
  rw [pow_two, ← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff,
    Subgroup.mem_subgroupOf] at h1
  exact h1

theorem sixFF_ff7_aux_normal_of_conj {G : Type} [Group G] {X Y : Subgroup G}
    (h : ∀ g ∈ Y, ∀ x ∈ X, g * x * g⁻¹ ∈ X) : (X.subgroupOf Y).Normal :=
  ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simpa using h (g : G) g.2 (n : G) hn⟩

theorem sixFF_ff7_aux_conj_of_normalIn {G : Type} [Group G] {X Tp : Subgroup G} (hX : X ≤ Tp)
    (hN : (X.subgroupOf Tp).Normal) : ∀ g ∈ Tp, ∀ x ∈ X, g * x * g⁻¹ ∈ X :=
  fun g hg x hx =>
    Subgroup.mem_subgroupOf.mp (hN.conj_mem ⟨x, hX hx⟩ (Subgroup.mem_subgroupOf.mpr hx) ⟨g, hg⟩)

theorem sixFF_ff7_aux_conj_central {G : Type} [Group G] {T V : Subgroup G}
    (hV : (center ↥T).map T.subtype = V) {g x : G} (hg : g ∈ T) (hx : x ∈ V) :
    g * x * g⁻¹ ∈ V := by
  rw [← hV] at hx ⊢
  obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hx
  refine Subgroup.mem_map.mpr ⟨z, hz, ?_⟩
  have hc := congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨g, hg⟩)
  change g * (z : G) = (z : G) * g at hc
  change (z : G) = g * (z : G) * g⁻¹
  rw [hc, mul_inv_cancel_right]

theorem sixFF_ff7_aux_closure_conj {G : Type} [Group G] {M T : Subgroup G}
    (hM : ∀ g ∈ T, ∀ x ∈ M, g * x * g⁻¹ ∈ M) {g x : G} (hg : g ∈ T)
    (hx : x ∈ Subgroup.closure {y : G | ∃ z ∈ M, y = z * z}) :
    g * x * g⁻¹ ∈ Subgroup.closure {y : G | ∃ z ∈ M, y = z * z} := by
  refine sixFF_ff3a_conj_closure (g := g) (X := {y : G | ∃ z ∈ M, y = z * z}) ?_ x hx
  rintro _ ⟨z, hz, rfl⟩
  exact Subgroup.subset_closure ⟨g * z * g⁻¹, hM g hg z hz, by group⟩

theorem sixFF_ff7_aux_axis (k i : Axis) : k = i ∨ k = i.swap := by
  cases k <;> cases i <;> simp [Axis.swap]

theorem sixFF_ff7_aux_le_of_center {G : Type} [Group G] {H V : Subgroup G}
    (h : (center ↥H).map H.subtype = V) : V ≤ H := by
  rintro _ hy
  rw [← h] at hy
  obtain ⟨z, _, rfl⟩ := Subgroup.mem_map.mp hy
  exact z.2

theorem sixFF_ff7_aux_sq_of_closure {G : Type} [Group G] {M N : Subgroup G}
    (hN : Subgroup.closure {x : G | ∃ y ∈ M, x = y * y} = N) {y : G} (hy : y ∈ M) :
    y * y ∈ N := by
  rw [← hN]
  exact Subgroup.subset_closure ⟨y, hy, rfl⟩

theorem sixFF_ff7_aux_sq_of_maximal {G : Type} [Group G] {A B₁ B₂ T N : Subgroup G}
    [(N.subgroupOf T).Normal] (hmax : SixG.MNMaximal A B₁ B₂ T N) {y : G} (hyB : y ∈ B₂)
    (hyT : y ∈ T) : y * y ∈ N := by
  have hmem : IsElementaryAbelian 2
      ↥((B₂.subgroupOf T).map (QuotientGroup.mk' (N.subgroupOf T))) :=
    ((hmax ((B₂.subgroupOf T).map (QuotientGroup.mk' (N.subgroupOf T)))).mpr (Or.inr rfl)).1.2
  exact sixFF_ff7_aux_sq_mem _ hmem ⟨y, hyT⟩
    (Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hyB))

theorem sixFF_ff7_aux_quot_of_sq {G : Type} [Group G] {X Y : Subgroup G}
    (hnorm : (X.subgroupOf Y).Normal) (hsq : ∀ y ∈ Y, y * y ∈ X) :
    ∃ _ : (X.subgroupOf Y).Normal, IsElementaryAbelian 2 (↥Y ⧸ X.subgroupOf Y) := by
  refine ⟨hnorm, ?_⟩
  haveI := hnorm
  exact sixFF_ff7_aux_quot_ea (fun y => hsq (y : G) y.2)

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {L : Subgroup G} {K : Type} [Field K]
  [CharP K 2] [Finite K] {n : ℕ} {φ : L ≃* antiSp K} {t : G} {i : Axis}

theorem sixFF_ff7_aux_Mc_le_Mhat (k : Axis) : Mc φ t i ≤ Mhat φ t i k := le_sup_left

theorem sixFF_ff7_aux_Mhat_le_S (k : Axis) : Mhat φ t i k ≤ S φ t i := by
  cases k
  · exact le_sup_left
  · exact le_sup_right

theorem sixFF_ff7_aux_Mc_le_S : Mc φ t i ≤ S φ t i :=
  (sixFF_ff7_aux_Mc_le_Mhat Axis.one).trans (sixFF_ff7_aux_Mhat_le_S Axis.one)

theorem sixFF_ff7_aux_Kc_le_S (hH : SixHConclusion φ t i) : Kc φ t i.swap ≤ S φ t i := by
  rw [← hH.sq_Mhat_j, Subgroup.closure_le]
  rintro _ ⟨y, hy, rfl⟩
  exact (S φ t i).mul_mem (sixFF_ff7_aux_Mhat_le_S i.swap hy)
    (sixFF_ff7_aux_Mhat_le_S i.swap hy)

theorem sixFF_ff7_aux_Kc_le_Dstar : Kc φ t i.swap ≤ Dstar φ t i := le_sup_right

theorem sixFF_ff7_aux_Mhat_le_Dstar : Mhat φ t i i ≤ Dstar φ t i := le_sup_left

theorem sixFF_ff7_aux_Dstar_le_S (hH : SixHConclusion φ t i) : Dstar φ t i ≤ S φ t i :=
  sup_le (sixFF_ff7_aux_Mhat_le_S i) (sixFF_ff7_aux_Kc_le_S hH)

theorem sixFF_ff7_aux_S_le_Tplus (hH : SixHConclusion φ t i) : S φ t i ≤ Tplus φ t i := by
  rw [← hH.sup_t]
  exact le_sup_left

theorem sixFF_ff7_aux_Mhat_le_Tplus (hH : SixHConclusion φ t i) (k : Axis) :
    Mhat φ t i k ≤ Tplus φ t i :=
  (sixFF_ff7_aux_Mhat_le_S k).trans (sixFF_ff7_aux_S_le_Tplus hH)

theorem sixFF_ff7_aux_Dstar_le_Tplus (hH : SixHConclusion φ t i) :
    Dstar φ t i ≤ Tplus φ t i :=
  (sixFF_ff7_aux_Dstar_le_S hH).trans (sixFF_ff7_aux_S_le_Tplus hH)

theorem sixFF_ff7_aux_Mc_le_Tplus (hH : SixHConclusion φ t i) : Mc φ t i ≤ Tplus φ t i :=
  sixFF_ff7_aux_Mc_le_S.trans (sixFF_ff7_aux_S_le_Tplus hH)

theorem sixFF_ff7_aux_Kc_le_Tplus (hH : SixHConclusion φ t i) :
    Kc φ t i.swap ≤ Tplus φ t i :=
  (sixFF_ff7_aux_Kc_le_S hH).trans (sixFF_ff7_aux_S_le_Tplus hH)

theorem sixFF_ff7_aux_Fj_le_Mc (hH : SixHConclusion φ t i) :
    F φ t ⊓ D φ t i.swap ≤ Mc φ t i := by
  rw [← hH.inf_M_K]
  exact inf_le_left

theorem sixFF_ff7_aux_Fj_le_Tplus (hH : SixHConclusion φ t i) :
    F φ t ⊓ D φ t i.swap ≤ Tplus φ t i :=
  (sixFF_ff7_aux_Fj_le_Mc hH).trans (sixFF_ff7_aux_Mc_le_Tplus hH)

theorem sixFF_ff7_aux_Mhat_le_DM (k : Axis) :
    Mhat φ t i k ≤ Dstar φ t i ⊔ Mhat φ t i i.swap := by
  rcases sixFF_ff7_aux_axis k i with h | h
  · rw [h]
    exact le_sup_of_le_left sixFF_ff7_aux_Mhat_le_Dstar
  · rw [h]
    exact le_sup_right

theorem sixFF_ff7_aux_S_le_DM : S φ t i ≤ Dstar φ t i ⊔ Mhat φ t i i.swap :=
  sup_le (sixFF_ff7_aux_Mhat_le_DM Axis.one) (sixFF_ff7_aux_Mhat_le_DM Axis.two)

theorem sixFF_ff7_aux_U_le_Fj (hS : SCSetting L K n φ t i) :
    U φ i ≤ F φ t ⊓ D φ t i.swap :=
  (GomiFusion.pull_mono φ (FullCenter.rootU_le_center i)).trans
    (FullCenterTorus.ZP_le_Fi hS.fc i.swap)

theorem sixFF_ff7_aux_U_le_Mhat (hH : SixHConclusion φ t i) : U φ i ≤ Mhat φ t i i :=
  sixFF_ff7_aux_le_of_center hH.center_Mhat_i

theorem sixFF_ff7_aux_U_le_Mc (hS : SCSetting L K n φ t i) (hH : SixHConclusion φ t i) :
    U φ i ≤ Mc φ t i :=
  (sixFF_ff7_aux_U_le_Fj hS).trans (sixFF_ff7_aux_Fj_le_Mc hH)

theorem sixFF_ff7_aux_U_le_A : U φ i ≤ A φ i :=
  GomiFusion.pull_mono φ (FullCenter.rootU_le_rootA i)

theorem sixFF_ff7_aux_sq_Mhat_i (hH : SixHConclusion φ t i) {y : G} (hy : y ∈ Mhat φ t i i) :
    y * y ∈ U φ i :=
  sixFF_ff7_aux_sq_of_closure hH.sq_Mhat_i hy

theorem sixFF_ff7_aux_sq_Mhat_j (hH : SixHConclusion φ t i) {y : G}
    (hy : y ∈ Mhat φ t i i.swap) : y * y ∈ Kc φ t i.swap :=
  sixFF_ff7_aux_sq_of_closure hH.sq_Mhat_j hy

theorem sixFF_ff7_aux_U_exp (hS : SCSetting L K n φ t i) {y : G} (hy : y ∈ U φ i) :
    y * y = 1 :=
  SingleComm.A_mul_self hS.fc i (sixFF_ff7_aux_U_le_A hy)

theorem sixFF_ff7_aux_Kc_le_B2 : Kc φ t i.swap ≤ Mc φ t i ⊔ Kc φ t i.swap := le_sup_right

theorem sixFF_ff7_aux_sqK (hH : SixHConclusion φ t i) {a : G} (ha : a ∈ Kc φ t i.swap) :
    a * a ∈ U φ i := by
  obtain ⟨hnD, hmaxD⟩ := hH.maximal_Dstar
  exact sixFF_ff7_aux_sq_of_maximal hmaxD (sixFF_ff7_aux_Kc_le_B2 ha)
    (sixFF_ff7_aux_Kc_le_Dstar ha)

theorem sixFF_ff7_aux_conj_U (hH : SixHConclusion φ t i) {g x : G} (hg : g ∈ Tplus φ t i)
    (hx : x ∈ U φ i) : g * x * g⁻¹ ∈ U φ i :=
  sixFF_ff7_aux_conj_central hH.center_Tplus hg hx

theorem sixFF_ff7_aux_conj_Mc (hH : SixHConclusion φ t i) {g x : G} (hg : g ∈ Tplus φ t i)
    (hx : x ∈ Mc φ t i) : g * x * g⁻¹ ∈ Mc φ t i :=
  sixFF_ff7_aux_conj_of_normalIn hH.normal_M.1 hH.normal_M.2.1 g hg x hx

theorem sixFF_ff7_aux_conj_Mhat (hH : SixHConclusion φ t i) (k : Axis) {g x : G}
    (hg : g ∈ Tplus φ t i) (hx : x ∈ Mhat φ t i k) : g * x * g⁻¹ ∈ Mhat φ t i k :=
  sixFF_ff7_aux_conj_of_normalIn (hH.normal_Mhat k).1 (hH.normal_Mhat k).2.1 g hg x hx

theorem sixFF_ff7_aux_conj_Dstar (hH : SixHConclusion φ t i) {g x : G} (hg : g ∈ Tplus φ t i)
    (hx : x ∈ Dstar φ t i) : g * x * g⁻¹ ∈ Dstar φ t i :=
  sixFF_ff7_aux_conj_of_normalIn hH.normal_Dstar.1 hH.normal_Dstar.2.1 g hg x hx

theorem sixFF_ff7_aux_conj_Kc (hH : SixHConclusion φ t i) {g x : G} (hg : g ∈ Tplus φ t i)
    (hx : x ∈ Kc φ t i.swap) : g * x * g⁻¹ ∈ Kc φ t i.swap := by
  rw [← hH.sq_Mhat_j] at hx ⊢
  exact sixFF_ff7_aux_closure_conj (M := Mhat φ t i i.swap) (T := Tplus φ t i)
    (fun g hg x hx => sixFF_ff7_aux_conj_Mhat hH i.swap hg hx) hg hx

theorem sixFF_ff7_aux_conj_Fj (hH : SixHConclusion φ t i) {g x : G} (hg : g ∈ Tplus φ t i)
    (hx : x ∈ F φ t ⊓ D φ t i.swap) : g * x * g⁻¹ ∈ F φ t ⊓ D φ t i.swap := by
  rw [← hH.inf_M_K] at hx ⊢
  exact Subgroup.mem_inf.mpr ⟨sixFF_ff7_aux_conj_Mc hH hg (Subgroup.mem_inf.mp hx).1,
    sixFF_ff7_aux_conj_Kc hH hg (Subgroup.mem_inf.mp hx).2⟩

theorem sixFF_ff7_aux_q0 (hS : SCSetting L K n φ t i) :
    ∃ _ : ((⊥ : Subgroup G).subgroupOf (U φ i)).Normal,
      IsElementaryAbelian 2 (↥(U φ i) ⧸ (⊥ : Subgroup G).subgroupOf (U φ i)) :=
  sixFF_ff7_aux_quot_of_sq
    (sixFF_ff7_aux_normal_of_conj (fun g _ x hx => by rw [Subgroup.mem_bot.mp hx]; simp))
    (fun y hy => Subgroup.mem_bot.mpr (sixFF_ff7_aux_U_exp hS hy))

theorem sixFF_ff7_aux_q1 (hH : SixHConclusion φ t i) :
    ∃ _ : ((U φ i).subgroupOf (F φ t ⊓ D φ t i.swap)).Normal,
      IsElementaryAbelian 2
        (↥(F φ t ⊓ D φ t i.swap) ⧸ (U φ i).subgroupOf (F φ t ⊓ D φ t i.swap)) :=
  sixFF_ff7_aux_quot_of_sq
    (sixFF_ff7_aux_normal_of_conj (fun g hg x hx =>
      sixFF_ff7_aux_conj_U hH (sixFF_ff7_aux_Fj_le_Tplus hH hg) hx))
    (fun y hy =>
      sixFF_ff7_aux_sq_Mhat_i hH (sixFF_ff7_aux_Mc_le_Mhat i (sixFF_ff7_aux_Fj_le_Mc hH hy)))

theorem sixFF_ff7_aux_q2 (hH : SixHConclusion φ t i) :
    ∃ _ : ((F φ t ⊓ D φ t i.swap).subgroupOf (Mc φ t i)).Normal,
      IsElementaryAbelian 2
        (↥(Mc φ t i) ⧸ (F φ t ⊓ D φ t i.swap).subgroupOf (Mc φ t i)) :=
  sixFF_ff7_aux_quot_of_sq
    (sixFF_ff7_aux_normal_of_conj (fun g hg x hx =>
      sixFF_ff7_aux_conj_Fj hH (sixFF_ff7_aux_Mc_le_Tplus hH hg) hx))
    (fun y hy => by
      rw [← hH.inf_M_K]
      exact Subgroup.mem_inf.mpr ⟨(Mc φ t i).mul_mem hy hy,
        sixFF_ff7_aux_sq_Mhat_j hH (sixFF_ff7_aux_Mc_le_Mhat i.swap hy)⟩)

theorem sixFF_ff7_aux_q3 (hS : SCSetting L K n φ t i) (hH : SixHConclusion φ t i) :
    ∃ _ : ((Mc φ t i).subgroupOf (Mhat φ t i i)).Normal,
      IsElementaryAbelian 2 (↥(Mhat φ t i i) ⧸ (Mc φ t i).subgroupOf (Mhat φ t i i)) :=
  sixFF_ff7_aux_quot_of_sq
    (sixFF_ff7_aux_normal_of_conj (fun g hg x hx =>
      sixFF_ff7_aux_conj_Mc hH (sixFF_ff7_aux_Mhat_le_Tplus hH i hg) hx))
    (fun y hy => sixFF_ff7_aux_U_le_Mc hS hH (sixFF_ff7_aux_sq_Mhat_i hH hy))

theorem sixFF_ff7_aux_q4 (hH : SixHConclusion φ t i) :
    ∃ _ : ((Mhat φ t i i).subgroupOf (Dstar φ t i)).Normal,
      IsElementaryAbelian 2
        (↥(Dstar φ t i) ⧸ (Mhat φ t i i).subgroupOf (Dstar φ t i)) :=
  sixFF_ff7_aux_quot_of_sq
    (sixFF_ff7_aux_normal_of_conj (fun g hg x hx =>
      sixFF_ff7_aux_conj_Mhat hH i (sixFF_ff7_aux_Dstar_le_Tplus hH hg) hx))
    (fun y hy => by
      obtain ⟨n, hn, a, ha, rfl⟩ := sixH_g8_mem_sup_mul
        (N := Mhat φ t i i) (A := Kc φ t i.swap)
        (fun a ha n hn => sixFF_ff7_aux_conj_Mhat hH i (sixFF_ff7_aux_Kc_le_Tplus hH ha) hn) hy
      have e : (n * a) * (n * a) = n * (a * n * a⁻¹) * (a * a) := by group
      rw [e]
      exact (Mhat φ t i i).mul_mem
        ((Mhat φ t i i).mul_mem hn
          (sixFF_ff7_aux_conj_Mhat hH i (sixFF_ff7_aux_Kc_le_Tplus hH ha) hn))
        (sixFF_ff7_aux_U_le_Mhat hH (sixFF_ff7_aux_sqK hH ha)))

theorem sixFF_ff7_aux_q5 (hH : SixHConclusion φ t i) :
    ∃ _ : ((Dstar φ t i).subgroupOf (S φ t i)).Normal,
      IsElementaryAbelian 2 (↥(S φ t i) ⧸ (Dstar φ t i).subgroupOf (S φ t i)) :=
  sixFF_ff7_aux_quot_of_sq
    (sixFF_ff7_aux_normal_of_conj (fun g hg x hx =>
      sixFF_ff7_aux_conj_Dstar hH (sixFF_ff7_aux_S_le_Tplus hH hg) hx))
    (fun y hy => by
      obtain ⟨n, hn, a, ha, rfl⟩ := sixH_g8_mem_sup_mul
        (N := Dstar φ t i) (A := Mhat φ t i i.swap)
        (fun a ha n hn => sixFF_ff7_aux_conj_Dstar hH (sixFF_ff7_aux_Mhat_le_Tplus hH i.swap ha) hn)
        (sixFF_ff7_aux_S_le_DM hy)
      have e : (n * a) * (n * a) = n * (a * n * a⁻¹) * (a * a) := by group
      rw [e]
      exact (Dstar φ t i).mul_mem
        ((Dstar φ t i).mul_mem hn
          (sixFF_ff7_aux_conj_Dstar hH (sixFF_ff7_aux_Mhat_le_Tplus hH i.swap ha) hn))
        (sixFF_ff7_aux_Kc_le_Dstar (sixFF_ff7_aux_sq_Mhat_j hH ha)))

theorem sixFF_ff7_aux_normS_of {X : Subgroup G}
    (hX : ∀ g ∈ Tplus φ t i, ∀ x ∈ X, g * x * g⁻¹ ∈ X) (hH : SixHConclusion φ t i) :
    (X.subgroupOf (S φ t i)).Normal :=
  sixFF_ff7_aux_normal_of_conj (fun g hg x hx => hX g (sixFF_ff7_aux_S_le_Tplus hH hg) x hx)

theorem sixFF_ff7_aux_normS_bot : ((⊥ : Subgroup G).subgroupOf (S φ t i)).Normal :=
  sixFF_ff7_aux_normal_of_conj (fun g _ x hx => by rw [Subgroup.mem_bot.mp hx]; simp)

theorem sixFF_ff7_aux_normS (hH : SixHConclusion φ t i) :
    ∀ k : Fin 7, ((ffSeries φ t i k).subgroupOf (S φ t i)).Normal := by
  intro k
  fin_cases k
  · exact sixFF_ff7_aux_normS_bot
  · exact sixFF_ff7_aux_normS_of (X := U φ i)
      (fun g hg x hx => sixFF_ff7_aux_conj_U hH hg hx) hH
  · exact sixFF_ff7_aux_normS_of (X := F φ t ⊓ D φ t i.swap)
      (fun g hg x hx => sixFF_ff7_aux_conj_Fj hH hg hx) hH
  · exact sixFF_ff7_aux_normS_of (X := Mc φ t i)
      (fun g hg x hx => sixFF_ff7_aux_conj_Mc hH hg hx) hH
  · exact sixFF_ff7_aux_normS_of (X := Mhat φ t i i)
      (fun g hg x hx => sixFF_ff7_aux_conj_Mhat hH i hg hx) hH
  · exact sixFF_ff7_aux_normS_of (X := Dstar φ t i)
      (fun g hg x hx => sixFF_ff7_aux_conj_Dstar hH hg hx) hH
  · exact sixFF_ff7_aux_normal_of_conj (fun g hg x hx =>
      (S φ t i).mul_mem ((S φ t i).mul_mem hg hx) ((S φ t i).inv_mem hg))

theorem sixFF_ff7_aux_chain (hS : SCSetting L K n φ t i) (hH : SixHConclusion φ t i) :
    ∀ k : Fin 6, ffSeries φ t i k.castSucc ≤ ffSeries φ t i k.succ := by
  intro k
  fin_cases k
  · exact bot_le
  · exact sixFF_ff7_aux_U_le_Fj hS
  · exact sixFF_ff7_aux_Fj_le_Mc hH
  · exact sixFF_ff7_aux_Mc_le_Mhat i
  · exact sixFF_ff7_aux_Mhat_le_Dstar
  · exact sixFF_ff7_aux_Dstar_le_S hH

theorem sixFF_ff7_aux_quots (hS : SCSetting L K n φ t i) (hH : SixHConclusion φ t i) :
    ∀ k : Fin 6, ∃ _ : ((ffSeries φ t i k.castSucc).subgroupOf (ffSeries φ t i k.succ)).Normal,
      IsElementaryAbelian 2 (↥(ffSeries φ t i k.succ) ⧸
        (ffSeries φ t i k.castSucc).subgroupOf (ffSeries φ t i k.succ)) := by
  intro k
  fin_cases k
  · exact sixFF_ff7_aux_q0 hS
  · exact sixFF_ff7_aux_q1 hH
  · exact sixFF_ff7_aux_q2 hH
  · exact sixFF_ff7_aux_q3 hS hH
  · exact sixFF_ff7_aux_q4 hH
  · exact sixFF_ff7_aux_q5 hH

theorem sixFF_ff7_aux_card1 : Nat.card (ffSeries φ t i 1) = Nat.card K :=
  FullCenter.FCHyp.card_U i

theorem sixFF_ff7_aux_card2 (hS : SCSetting L K n φ t i) :
    Nat.card (ffSeries φ t i 2) = Nat.card K ^ 3 :=
  FullCenterTorus.card_Fi hS.fc i.swap

theorem sixFF_ff7_aux_card3 (hS : SCSetting L K n φ t i) :
    Nat.card (ffSeries φ t i 3) = Nat.card K ^ 5 :=
  NextCores.card_M hS.fc i hS.ne_bot hS.eq_bot

theorem sixFF_ff7_aux_card4 (hS : SCSetting L K n φ t i) :
    Nat.card (ffSeries φ t i 4) = Nat.card K ^ 7 :=
  SixF.card_Mhat hS.fc i hS.ne_bot hS.eq_bot

theorem sixFF_ff7_aux_card5 (hH : SixHConclusion φ t i) :
    Nat.card (ffSeries φ t i 5) = Nat.card K ^ 8 :=
  hH.card_Dstar

theorem sixFF_ff7_aux_card6 (hH : SixHConclusion φ t i) :
    Nat.card (ffSeries φ t i 6) = Nat.card K ^ 10 :=
  hH.card_S

theorem sixFF_ff7
    (hSel : CFSG.LocalAnalysis.EvenBN.GMSK.FixedRootSelector fun D _ => CFSG.Blueprint.Catalog D)
    (hS : SCSetting L K n φ t i) (hH : SixHConclusion φ t i) : FF7Concl φ t i := by
  unfold FF7Concl
  exact ⟨sixFF_ff7_aux_normS hH, sixFF_ff7_aux_chain hS hH, sixFF_ff7_aux_quots hS hH,
    sixFF_ff7_aux_card1 (φ := φ) (t := t) (i := i), sixFF_ff7_aux_card2 hS,
    sixFF_ff7_aux_card3 hS, sixFF_ff7_aux_card4 hS, sixFF_ff7_aux_card5 hH,
    sixFF_ff7_aux_card6 hH⟩

end Steps

end SingleCommParts

end CFSG.LocalAnalysis.SymplecticFourStandard
