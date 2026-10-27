module

public import CFSG.Quasithin.Background.F918D1
public import CFSG.Quasithin.Background.F918D7
public import CFSG.Quasithin.EmptyFaithful.A38c11FF
public import CFSG.Quasithin.EmptyFaithful.A38c11Group

public section

namespace CFSG.Quasithin.A38c16

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F7
open scoped Pointwise commutatorElement

section Transport

variable {G : Type} [Group G]

@[expose] def IsNatSec (K Z U J : Subgroup G) : Prop :=
  Z ≤ J ∧ J ≤ U ∧ mIdx J Z = 3 ∧ IsIrredOnSection K J Z

theorem kInv_conjSub [Finite G] {K Z U H W : Subgroup G} (hKH : K ≤ H)
    (hZc : ∀ z ∈ Z, ∀ h ∈ H, h * z * h⁻¹ = z)
    (hQ : ∀ c ∈ pCoreOf 2 H, ∀ u ∈ U, c * u * c⁻¹ * u⁻¹ ∈ Z)
    (hZW : Z ≤ W) (hWU : W ≤ U) (hWK : ∀ k ∈ K, ∀ w ∈ W, k * w * k⁻¹ ∈ W)
    {x : G} (hxK : ∀ k ∈ K, ∃ k₁ ∈ K, ∃ c ∈ pCoreOf 2 H, x⁻¹ * k * x = k₁ * c) :
    ∀ k ∈ K, ∀ w ∈ conjSub x W, k * w * k⁻¹ ∈ conjSub x W := by
  intro k hk w hw
  rw [mem_conjSub] at hw ⊢
  obtain ⟨k₁, hk₁, c, hc, hkc⟩ := hxK k hk
  have hw₀U : x⁻¹ * w * x ∈ U := hWU hw
  have hcw : c * (x⁻¹ * w * x) * c⁻¹ * (x⁻¹ * w * x)⁻¹ ∈ Z := hQ c hc _ hw₀U
  set w₀ := x⁻¹ * w * x with hw₀
  have e1 : x⁻¹ * (k * w * k⁻¹) * x = (k₁ * c) * w₀ * (k₁ * c)⁻¹ := by
    rw [← hkc, hw₀]; group
  have e2 : (k₁ * c) * w₀ * (k₁ * c)⁻¹ =
      k₁ * (c * w₀ * c⁻¹ * w₀⁻¹) * k₁⁻¹ * (k₁ * w₀ * k₁⁻¹) := by group
  rw [e1, e2]
  refine W.mul_mem ?_ (hWK k₁ hk₁ w₀ hw)
  have hz := hZc _ hcw k₁ (hKH hk₁)
  rw [hz]
  exact hZW hcw

theorem le_normalizer_of_forall_conj {K W : Subgroup G} (h : ∀ k ∈ K, ∀ w ∈ W, k * w * k⁻¹ ∈ W) :
    K ≤ Subgroup.normalizer (W : Set G) := by
  intro k hk
  rw [Subgroup.mem_normalizer_iff]
  intro w
  refine ⟨fun hw => h k hk w hw, fun hw => ?_⟩
  have := h k⁻¹ (K.inv_mem hk) _ hw
  simpa [mul_assoc] using this

theorem isNatSec_conjSub [Finite G] {K Z U H J : Subgroup G} (hKH : K ≤ H)
    (hZc : ∀ z ∈ Z, ∀ h ∈ H, h * z * h⁻¹ = z)
    (hUH : ∀ h ∈ H, ∀ u ∈ U, h * u * h⁻¹ ∈ U)
    (hQ : ∀ c ∈ pCoreOf 2 H, ∀ u ∈ U, c * u * c⁻¹ * u⁻¹ ∈ Z)
    {x : G} (hx : x ∈ H)
    (hxK : ∀ k ∈ K, ∃ k₁ ∈ K, ∃ c ∈ pCoreOf 2 H, x⁻¹ * k * x = k₁ * c)
    (hxK' : ∀ k ∈ K, ∃ k₁ ∈ K, ∃ c ∈ pCoreOf 2 H, x * k * x⁻¹ = k₁ * c)
    (hJ : IsNatSec K Z U J) : IsNatSec K Z U (conjSub x J) := by
  obtain ⟨hZJ, hJU, hm, hirr⟩ := hJ
  obtain ⟨hZJ', hKJ, hKZ, hmin⟩ := hirr
  have hxinv : x⁻¹ ∈ H := H.inv_mem hx
  have hZx : conjSub x Z = Z := by
    ext z
    rw [mem_conjSub]
    constructor
    · intro hz
      have h1 := hZc _ hz x hx
      have h2 : x * (x⁻¹ * z * x) * x⁻¹ = z := by group
      rw [h2] at h1
      rw [h1]
      exact hz
    · intro hz
      have h1 := hZc z hz x⁻¹ hxinv
      simp only [inv_inv] at h1
      rw [h1]
      exact hz
  have hZxi : conjSub x⁻¹ Z = Z := by
    conv_lhs => rw [← hZx]
    exact conjSub_conjSub_inv x Z
  have hZle : Z ≤ conjSub x J := by
    intro z hz
    rw [mem_conjSub]
    have h1 := hZc z hz x⁻¹ hxinv
    simp only [inv_inv] at h1
    rw [h1]
    exact hZJ hz
  have hJxU : conjSub x J ≤ U := by
    intro w hw
    rw [mem_conjSub] at hw
    have h1 := hUH x hx _ (hJU hw)
    have e : x * (x⁻¹ * w * x) * x⁻¹ = w := by group
    rwa [e] at h1
  have hWKJ : ∀ k ∈ K, ∀ w ∈ J, k * w * k⁻¹ ∈ J := fun k hk w hw =>
    (Subgroup.mem_normalizer_iff.mp (hKJ hk) w).mp hw
  refine ⟨hZle, hJxU, ?_, ?_⟩
  · have h1 := F9.mIdx_conjSub x J Z
    rw [hZx] at h1
    rw [h1]
    exact hm
  · refine ⟨?_, ?_, ?_, ?_⟩
    · refine lt_of_le_of_ne hZle (fun h => hZJ'.ne ?_)
      have h2 : J = conjSub x⁻¹ (conjSub x J) := (conjSub_conjSub_inv x J).symm
      rw [h2, ← h, hZxi]
    · exact le_normalizer_of_forall_conj (kInv_conjSub hKH hZc hQ hZJ hJU hWKJ hxK)
    · exact hKZ
    · intro W' hZW' hW'J hKW'
      have hW'U : W' ≤ U := hW'J.trans hJxU
      have hW'inv : ∀ k ∈ K, ∀ w ∈ W', k * w * k⁻¹ ∈ W' := fun k hk w hw =>
        (Subgroup.mem_normalizer_iff.mp (hKW' hk) w).mp hw
      have hxK'' : ∀ k ∈ K, ∃ k₁ ∈ K, ∃ c ∈ pCoreOf 2 H, (x⁻¹)⁻¹ * k * x⁻¹ = k₁ * c := by
        simpa only [inv_inv] using hxK'
      have hback : conjSub x (conjSub x⁻¹ W') = W' := by
        simpa using conjSub_conjSub_inv x⁻¹ W'
      have hZW : Z ≤ conjSub x⁻¹ W' := by
        intro z hz
        rw [mem_conjSub]
        have h1 := hZc z hz x hx
        rw [inv_inv, h1]
        exact hZW' hz
      have hWJ : conjSub x⁻¹ W' ≤ J := by
        calc conjSub x⁻¹ W' ≤ conjSub x⁻¹ (conjSub x J) := conjSub_mono _ hW'J
          _ = J := conjSub_conjSub_inv x J
      have hKW : K ≤ Subgroup.normalizer (conjSub x⁻¹ W' : Set G) :=
        le_normalizer_of_forall_conj
          (kInv_conjSub hKH hZc hQ hZW' hW'U hW'inv hxK'')
      rcases hmin _ hZW hWJ hKW with h | h
      · left
        rw [← hback, h, hZx]
      · right
        rw [← hback, h]

end Transport

section Main

variable {G : Type} [Group G] [Finite G]

theorem comm_mem_pCoreOf_of_cComp {H K Kp : Subgroup G} (hodd : OddCoreModTwoTrivial H)
    (hK : K ∈ cComp H) (hKp : Kp ∈ cComp H) (hne : Kp ≠ K)
    (hnK : H ≤ Subgroup.normalizer (K : Set G)) (hnKp : H ≤ Subgroup.normalizer (Kp : Set G))
    {k y : G} (hk : k ∈ K) (hy : y ∈ Kp) : k⁻¹ * y⁻¹ * k * y ∈ pCoreOf 2 H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKH : K ≤ H := le_of_mem_cComp hK
  have hKpH : Kp ≤ H := le_of_mem_cComp hKp
  have hcK : k⁻¹ * y⁻¹ * k * y ∈ K := by
    have h1 : y⁻¹ * k * y ∈ K := by
      have := (Subgroup.mem_normalizer_iff.mp (hnK (hKpH (Kp.inv_mem hy))) k).mp hk
      simpa using this
    have h2 : k⁻¹ * y⁻¹ * k * y = k⁻¹ * (y⁻¹ * k * y) := by group
    rw [h2]
    exact K.mul_mem (K.inv_mem hk) h1
  have hcKp : k⁻¹ * y⁻¹ * k * y ∈ Kp := by
    have h1 : k⁻¹ * y⁻¹ * k ∈ Kp := by
      have := (Subgroup.mem_normalizer_iff.mp (hnKp (hKH (K.inv_mem hk))) y⁻¹).mp (Kp.inv_mem hy)
      simpa using this
    exact Kp.mul_mem h1 hy
  have hPn : ((K ⊓ Kp).subgroupOf K).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    refine ⟨K.mul_mem (K.mul_mem g.2 hn.1) (K.inv_mem g.2), ?_⟩
    have := (Subgroup.mem_normalizer_iff.mp (hnKp (hKH g.2)) (n : G)).mp hn.2
    simpa using this
  rcases normal_eq_top_or_map_le_solvRad hK ((K ⊓ Kp).subgroupOf K) with hP | hP
  · exfalso
    have hKKp : K ≤ Kp := by
      intro x hx
      have : (⟨x, hx⟩ : ↥K) ∈ (K ⊓ Kp).subgroupOf K := by rw [hP]; exact Subgroup.mem_top _
      exact (Subgroup.mem_subgroupOf.mp this).2
    exact hne (eq_of_le_cComp hKp hK hKKp).symm
  · have hc : k⁻¹ * y⁻¹ * k * y ∈ solvRad K := by
      apply hP
      exact ⟨⟨_, hcK⟩, Subgroup.mem_subgroupOf.mpr ⟨hcK, hcKp⟩, rfl⟩
    rw [solvRad_eq_pCoreOf_of_mem_cComp hodd hK] at hc
    exact A4.pCoreOf_le_of_subnormal 2 (subnormal_of_mem_cComp hK) hc

theorem commutator_le_sum_core {H K Kp H' V Z I : Subgroup G} {s : G}
    (hKH : K ≤ H) (hKpH : Kp ≤ H) (hH'H : H' ≤ H) (hKH' : K ≤ H')
    (hHK : H ≤ Subgroup.normalizer (K : Set G)) (hHKp : H ≤ Subgroup.normalizer (Kp : Set G))
    (hHeq : H = Kp ⊔ H') (hsH : s ∈ H) (hsK : s ∈ Subgroup.normalizer (K : Set G))
    (hUab : ∀ a ∈ conjClosure V H, ∀ b ∈ conjClosure V H, a * b = b * a)
    (hZc : ∀ z ∈ Z, ∀ h ∈ H, h * z * h⁻¹ = z) (hZV : Z ≤ V) (hZI : Z ≤ I)
    (hQ : ∀ c ∈ pCoreOf 2 H, ∀ u ∈ conjClosure V H, c * u * c⁻¹ * u⁻¹ ∈ Z)
    (hcomm : ∀ k ∈ K, ∀ y ∈ Kp, k⁻¹ * y⁻¹ * k * y ∈ pCoreOf 2 H)
    (hsup : ⁅conjClosure V H', K⁆ ⊔ Z = I ⊔ conjSub s I)
    (hI : mIdx I Z = 3 ∧ IsIrredOnSection K I Z) :
    ⁅conjClosure V H, K⁆ ⊔ Z ≤
      ⨆ (J : Subgroup G) (_ : Z ≤ J ∧ J ≤ conjClosure V H ∧ mIdx J Z = 3 ∧ IsIrredOnSection K J Z),
        J := by
  have hUN : H ≤ Subgroup.normalizer (conjClosure V H : Set G) := le_normalizer_conjClosure V H
  have hUH : ∀ h ∈ H, ∀ u ∈ conjClosure V H, h * u * h⁻¹ ∈ conjClosure V H := fun h hh u hu =>
    (Subgroup.mem_normalizer_iff.mp (hUN hh) u).mp hu
  have hU'U : conjClosure V H' ≤ conjClosure V H := conjClosure_mono le_rfl hH'H
  have hU'N : H' ≤ Subgroup.normalizer (conjClosure V H' : Set G) := le_normalizer_conjClosure V H'
  have hcommU' : ⁅conjClosure V H', K⁆ ≤ conjClosure V H' := by
    rw [Subgroup.commutator_le]
    intro u hu k hk
    have : k * u⁻¹ * k⁻¹ ∈ conjClosure V H' :=
      (Subgroup.mem_normalizer_iff.mp (hU'N (hKH' hk)) u⁻¹).mp ((conjClosure V H').inv_mem hu)
    have e : ⁅u, k⁆ = u * (k * u⁻¹ * k⁻¹) := by simp only [commutatorElement_def]; group
    rw [e]
    exact (conjClosure V H').mul_mem hu this
  have hZU : Z ≤ conjClosure V H := hZV.trans (le_conjClosure V H)
  have hXU : ⁅conjClosure V H', K⁆ ⊔ Z ≤ conjClosure V H := sup_le (hcommU'.trans hU'U) hZU
  have hIU : I ≤ conjClosure V H := le_sup_left.trans (hsup ▸ hXU)
  have hIJ : IsNatSec K Z (conjClosure V H) I := ⟨hZI, hIU, hI.1, hI.2⟩
  have hsK1 : ∀ k ∈ K, s⁻¹ * k * s ∈ K := fun k hk => by
    have := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer (K : Set G)).inv_mem hsK) k).mp hk
    simpa using this
  have hsK2 : ∀ k ∈ K, s * k * s⁻¹ ∈ K := fun k hk =>
    (Subgroup.mem_normalizer_iff.mp hsK k).mp hk
  have hsJ : IsNatSec K Z (conjClosure V H) (conjSub s I) :=
    isNatSec_conjSub hKH hZc hUH hQ hsH
      (fun k hk => ⟨s⁻¹ * k * s, hsK1 k hk, 1, Subgroup.one_mem _, by simp⟩)
      (fun k hk => ⟨s * k * s⁻¹, hsK2 k hk, 1, Subgroup.one_mem _, by simp⟩) hIJ
  have hyJ : ∀ y ∈ Kp, ∀ J, IsNatSec K Z (conjClosure V H) J →
      IsNatSec K Z (conjClosure V H) (conjSub y J) := by
    intro y hy J hJ
    refine isNatSec_conjSub hKH hZc hUH hQ (hKpH hy) (fun k hk => ⟨k, hk, _, hcomm k hk y hy, ?_⟩)
      (fun k hk => ⟨k, hk, _, hcomm k hk y⁻¹ (Kp.inv_mem hy), ?_⟩) hJ
    · group
    · group
  set target : Subgroup G :=
    ⨆ (J : Subgroup G) (_ : Z ≤ J ∧ J ≤ conjClosure V H ∧ mIdx J Z = 3 ∧ IsIrredOnSection K J Z), J
    with htarget
  have hle : ∀ J, IsNatSec K Z (conjClosure V H) J → J ≤ target := fun J hJ =>
    le_iSup₂ (f := fun (J : Subgroup G) (_ : Z ≤ J ∧ J ≤ conjClosure V H ∧ mIdx J Z = 3 ∧
      IsIrredOnSection K J Z) => J) J hJ
  have hIt : I ≤ target := hle I hIJ
  have hW₀t : conjClosure (⁅conjClosure V H', K⁆ ⊔ Z) Kp ≤ target := by
    refine conjClosure_le fun y hy a ha => ?_
    rw [hsup] at ha
    have h1 : y * a * y⁻¹ ∈ conjSub y (I ⊔ conjSub s I) := mul_mem_conjSub ha
    have h2 : conjSub y (I ⊔ conjSub s I) = conjSub y I ⊔ conjSub y (conjSub s I) := by
      unfold conjSub
      exact Subgroup.map_sup _ _ _
    rw [h2] at h1
    exact (sup_le (hle _ (hyJ y hy I hIJ)) (hle _ (hyJ y hy _ hsJ))) h1
  have hWU : conjClosure (⁅conjClosure V H', K⁆ ⊔ Z) Kp ≤ conjClosure V H := by
    refine conjClosure_le fun y hy a ha => hUH y (hKpH hy) a (hXU ha)
  have hmain : ⁅conjClosure V H, K⁆ ≤ conjClosure (⁅conjClosure V H', K⁆ ⊔ Z) Kp :=
    A38c11.commutator_le_of_invariant hKpH hHK (A38c11.exists_mul_of_sup (hH'H.trans hHKp) hHeq)
      hUab hWU (le_normalizer_conjClosure _ _)
      (le_sup_left.trans (le_conjClosure _ _))
  exact sup_le (hmain.trans hW₀t) (hZI.trans hIt)

theorem commutator_le_sum_natural
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK) (h56 : AsB56) (hD310 : D310)
    (hD391 : D391) (hNat : Insp14622Nat)
    {T M : Subgroup G} (S : Setting146 G T M) (hB : HypB146 T M)
    (c19 : Conc14619 T M) (c20 : Conc14620 T M)
    {K Kp : Subgroup G} (hK : K ∈ cComp (mcOf T)) (hKp : Kp ∈ cComp (mcOf T)) (hne : Kp ≠ K)
    (hnK : mcOf T ≤ Subgroup.normalizer (K : Set G))
    (hnKp : mcOf T ≤ Subgroup.normalizer (Kp : Set G))
    (hper : perfectCore (mcOf T) = K ⊔ Kp) (hL32 : KbarIsL3Two K) :
    ⁅uOfL22 T M, K⁆ ⊔ quasithinOmegaOneCenter T ≤
      ⨆ (J : Subgroup G) (_ : quasithinOmegaOneCenter T ≤ J ∧ J ≤ uOfL22 T M ∧
          mIdx J (quasithinOmegaOneCenter T) = 3 ∧
          IsIrredOnSection K J (quasithinOmegaOneCenter T)), J := by
  have hHTM : IsHTM T M (mcOf T) := S.isHTM_mcOf
  have hTH : T ≤ mcOf T := hHTM.1.1
  have hKH : K ≤ mcOf T := le_of_mem_cComp hK
  have hKpH : Kp ≤ mcOf T := le_of_mem_cComp hKp
  have hS' : IsSimpleGroup (KBar K) := (c19 _ hHTM).2 K hK
  obtain ⟨-, s, hs, hdyn⟩ := c20 _ hHTM K hK
  have hsT : s ∈ T := hs.1
  have hsK : s ∈ Subgroup.normalizer (K : Set G) := hs.2
  have hc21 : ∀ K ∈ cComp (mcOf T), Conc14621 T K :=
    stage14621_of_a3 h37 h38 h39 G T M S hB c19 c20
  obtain ⟨-, hHT⟩ := conc14623_one_of_a3 h37 h38 S hB c19 c20 hc21
  have hK₀ : conjClosure K T = K := by
    apply le_antisymm
    · refine conjClosure_le fun t ht z hz => ?_
      exact (Subgroup.mem_normalizer_iff.mp (hnK (hTH ht)) z).mp hz
    · exact le_conjClosure K T
  have hHle : conjClosure K T ⊔ T ≤ mcOf T := conjClosure_sup_le hKH hTH
  have hF : HypF918 T (VZ T M) (yOfL22 T M) (quasithinOmegaOneCenter T) (VZ T M)
      (conjClosure K T ⊔ T) K := hypF918_of_setting146 h37 h38 S hK hS'
  have hH' : SQTKGroup ↥(conjClosure K T ⊔ T) :=
    S.sqtkGroup_of_isHTM (S.isHTM_conjClosure_sup h37 h38 hK)
  have hNo := hasNoFaithfulFF_conjClosure_sup_of_normal h56 h37 h38 S c19 c20 hK hnK
  obtain ⟨I, hV₁I, hsup, hnat⟩ := case1_aux hF hH' rfl hK₀ hS' (Or.inl hL32) hsT hsK hdyn hD310
    hD391 hNat asI161A6_of n4Stmt_of hNo
  have hI : mIdx I (quasithinOmegaOneCenter T) = 3 ∧
      IsIrredOnSection K I (quasithinOmegaOneCenter T) := by
    rcases hnat with ⟨-, h3, hirr⟩ | ⟨hA6, -⟩
    · exact ⟨h3, hirr⟩
    · exact (not_kbarIsA6_of_kbarIsL3Two hL32 hA6).elim
  have hHeq : mcOf T = Kp ⊔ (conjClosure K T ⊔ T) := by
    refine le_antisymm ?_ (sup_le hKpH hHle)
    rw [hHT, hper, hK₀]
    exact sup_le (sup_le (le_sup_of_le_right (le_sup_of_le_left le_rfl)) le_sup_left)
      (le_sup_of_le_right le_sup_right)
  have hZc : ∀ z ∈ quasithinOmegaOneCenter T, ∀ h ∈ mcOf T, h * z * h⁻¹ = z := by
    intro z hz h hh
    have hcomm : z * h = h * z := Subgroup.mem_centralizer_iff.mp hh z hz
    calc h * z * h⁻¹ = z * h * h⁻¹ := by rw [hcomm]
      _ = z := by group
  have hUab : ∀ a ∈ conjClosure (VZ T M) (mcOf T), ∀ b ∈ conjClosure (VZ T M) (mcOf T),
      a * b = b * a := fun a ha b hb => isElemAbelian_comm (S.lemma_14_5_15_two hHTM) ha hb
  have hF98 := (S.lemma_14_5_14 (S.isHz_iff.mpr hHTM)).2
  have hQ : ∀ c ∈ pCoreOf 2 (mcOf T), ∀ u ∈ conjClosure (VZ T M) (mcOf T),
      c * u * c⁻¹ * u⁻¹ ∈ quasithinOmegaOneCenter T := by
    intro c hc u hu
    have hc' : c ∈ centralizerMod (quasithinOmegaOneCenter T) (mcOf T)
        (conjClosure (VZ T M) (mcOf T)) := hF98.toHypF91.pCoreOf_eq_centralizerMod ▸ hc
    exact hc'.2.2 u hu
  have hZV : quasithinOmegaOneCenter T ≤ VZ T M := le_conjClosure _ _
  exact commutator_le_sum_core hKH hKpH hHle ((le_conjClosure K T).trans le_sup_left) hnK hnKp
    hHeq (hTH hsT) hsK hUab hZc hZV hV₁I hQ
    (fun k hk y hy => comm_mem_pCoreOf_of_cComp (c19 _ hHTM).1 hK hKp hne hnK hnKp hk hy)
    hsup hI

end Main

end CFSG.Quasithin.A38c16
