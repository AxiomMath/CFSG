module

public import CFSG.LocalAnalysis.StandardType.GGLinearFusionSURepairBlock
public import CFSG.LocalAnalysis.StandardType.GGStdSubExistAdmissible

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank Matrix
open CFSG.SectionRank.OddCover (diagHom coe_diagHom)
open CFSG.RankThree.Classical (permGL)
open CFSG.ClassicalGroups.UnitaryFlag (unitarySU mem_unitarySU_iff)
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open CFSG.LieType.Universal.Unitary (SU antidiag conjTr)
open CFSG.LieType.BorelTits (unitaryInvolution)

namespace SURepair

variable {G : Type} [Group G] {n f : ℕ} {K : Type} [Field K]

@[expose] def GGFramePair (φ : ↥(unitarySU 2 f K n) →* G) (B : Subgroup G) (s t : Fin n) : Prop :=
  ∀ b ∈ B, ∀ τ : Fin n → Kˣ, SURep.GGFrameActs φ b τ → τ s = τ t

theorem mem_suPairs_of_frameActs (h : UnitaryFieldData 2 f K) {φ : ↥(unitarySU 2 f K n) →* G}
    {b : G} {τ : Fin n → Kˣ} (hb : SURep.GGFrameActs φ b τ) :
    (b, diagHom n τ) ∈ SUTorus.suPairs φ := by
  refine ⟨Subgroup.mem_normalizer_iff.mpr fun s => ⟨fun hs => SURep.conj_mem_unitarySU h hb.1 hs,
    fun hs => ?_⟩, fun u v huv => hb.2 u v huv⟩
  have h1 := SURep.conj_mem_unitarySU h (SURep.norm_inv_eq_one hb.1) hs
  have hinv : (diagHom n τ)⁻¹ = diagHom n τ⁻¹ := (map_inv _ τ).symm
  rwa [← hinv, inv_inv, show (diagHom n τ)⁻¹ * (diagHom n τ * s * (diagHom n τ)⁻¹) *
    diagHom n τ = s by group] at h1

theorem conjU_swapU_of_eq (h : UnitaryFieldData 2 f K) {τ : Fin n → Kˣ}
    (hτ : ∀ i, (τ i : K) ^ (2 ^ f + 1) = 1) {s t : Fin n} (hst : τ s = τ t) :
    SURep.conjU h hτ (SURep.swapU h s t) = SURep.swapU h s t := by
  apply Subtype.ext
  apply Units.ext
  ext a c
  rw [SURep.conjU_apply]
  change (τ a : K) * ((permGL (Equiv.swap s t) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) a c *
      ((τ c)⁻¹ : Kˣ) = ((permGL (Equiv.swap s t) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) a c
  rw [TableBUE.permGL_apply, Equiv.swap_inv]
  split_ifs with hac
  · have hτac : τ a = τ c := by
      rw [← hac]
      rcases eq_or_ne a s with has | has
      · rw [has, Equiv.swap_apply_left, hst]
      · rcases eq_or_ne a t with hat | hat
        · rw [hat, Equiv.swap_apply_right, hst]
        · rw [Equiv.swap_apply_of_ne_of_ne has hat]
    rw [mul_one, hτac, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  · rw [mul_zero, zero_mul]

theorem map_swapU_ne_one (h : UnitaryFieldData 2 f K) {φ : ↥(unitarySU 2 f K n) →* G}
    (hker : SURep.GGFrameKer φ) {s t : Fin n} (hst : s ≠ t) : φ (SURep.swapU h s t) ≠ 1 := by
  intro h1
  obtain ⟨c, hc⟩ := hker _ h1
  have h2 := congrFun (congrFun hc s) t
  change ((permGL (Equiv.swap s t) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) s t = _ at h2
  rw [TableBUE.permGL_apply, Equiv.swap_inv, Equiv.swap_apply_left, ite_eq_left rfl,
    Matrix.scalar_apply, diagonal_apply_ne _ hst] at h2
  exact one_ne_zero h2

theorem swapU_mul_self (h : UnitaryFieldData 2 f K) (s t : Fin n) :
    SURep.swapU h s t * SURep.swapU h s t = 1 := by
  apply Subtype.ext
  change (permGL (Equiv.swap s t) : GL (Fin n) K) * permGL (Equiv.swap s t) = 1
  rw [← map_mul, Equiv.swap_mul_self, map_one]

section Core

variable {G : Type} [Group G] [Finite G] {m f : ℕ} {K : Type} [Field K]

theorem bstar_inf_centralizer_le_of_pair (h : UnitaryFieldData 2 f K) (hf : 2 ≤ f)
    (hn : 3 ≤ m + 1) {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J) (hpq : p ∣ 2 ^ f + 1)
    {φ : ↥(unitarySU 2 f K (m + 1)) →* G}
    (hker : φ.ker ≤ Subgroup.center ↥(unitarySU 2 f K (m + 1))) (hLφ : L ≤ φ.range)
    (hframe : ∀ b ∈ Bs, SURep.GGFrameDiagU φ b)
    (hpair : B = Bs ∨ ∃ s t : Fin (m + 1), s ≠ t ∧ GGFramePair φ B s t) :
    Bs ⊓ Subgroup.centralizer (J : Set G) ≤ D := by
  have hDB : D = B ⊓ Subgroup.centralizer (J : Set G) := hcfg.2.2.1.2.2.2.2.2.2
  rcases hpair with hBB | ⟨s, t, hst, hBst⟩
  · rw [← hBB, ← hDB]
  classical
  have : Finite K := h.finite
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := h.charP
  have hp : p.Prime := hcfg.1.2.2.2.2.2.1.1
  have hp2 : p ≠ 2 := hcfg.1.2.2.2.2.2.1.2.1
  have hS : LargeEvenSStar p B x L := hcfg.1.2.2.2.2.2.2.1
  have hBBs : B ≤ Bs := hcfg.2.1.1
  have hDB' : D ≤ B := hcfg.2.2.1.1
  have hxD : x ∈ D := hcfg.2.2.1.2.2.2.1
  have hxB : x ∈ B := hS.2.1
  have hxBs : x ∈ Bs := hBBs hxB
  have hnq : (m + 1, 2 ^ f) ≠ (3, 2) := fun h' => by
    have h1 : 2 ^ f = 2 := congrArg Prod.snd h'
    have : 2 ^ 2 ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
    omega
  have hkerU : SURep.GGFrameKer φ := SURep.ggFrameKer_of_ker_le_center h.card_eq_sq hn hnq hker
  let δ : G → Fin (m + 1) → Kˣ := fun g => if hg : SURep.GGFrameDiagU φ g then hg.choose else 1
  have hδ : ∀ b ∈ Bs, SURep.GGFrameActs φ b (δ b) := by
    intro b hb
    have hg := hframe b hb
    simp only [δ, hg, ↓reduceDIte]
    exact hg.choose_spec
  have hδp : ∀ b ∈ Bs, (b, diagHom (m + 1) (δ b)) ∈ SUTorus.suPairs φ :=
    fun b hb => mem_suPairs_of_frameActs h (hδ b hb)
  have hδx : ∀ e ∈ ({x} : Set G), (e, diagHom (m + 1) (δ e)) ∈ SUTorus.suPairs φ := by
    intro e he
    rw [Set.mem_singleton_iff.mp he]
    exact hδp x hxBs
  have hδD : ∀ e ∈ (D : Set G), (e, diagHom (m + 1) (δ e)) ∈ SUTorus.suPairs φ :=
    fun e he => hδp e (hBBs (hDB' he))
  have hLc : IsComponentOf L (φ.range ⊓ Subgroup.centralizer ({x} : Set G)) :=
    CFSG.LocalAnalysis.ComponentInitial.isComponentOf_of_le hS.2.2.2.1
      (le_inf hLφ hS.2.2.2.1.1) inf_le_right
  obtain ⟨i₀, hLI⟩ := SUTorus.exists_le_map_blockSU h hp hpq hker hδx hLc
  set IL := LinTorus.diagClass ({x} : Set G) δ i₀ with hIL
  have hIL2 : 2 ≤ IL.card := by
    by_contra hlt
    have hIL1 : IL = {i₀} := Finset.eq_singleton_iff_unique_mem.mpr
      ⟨LinTorus.self_mem_diagClass _ _ _, fun j hj => Finset.card_le_one.mp (by omega) j hj i₀
        (LinTorus.self_mem_diagClass _ _ _)⟩
    rw [hIL1, SUTorus.blockSU_singleton h, Subgroup.map_bot] at hLI
    apply commutator_ne_bot_of_isQuasisimple hLc.2.2
    rw [le_bot_iff.mp hLI]
    exact Subgroup.commutator_bot_left _
  have hsubIL := SUTorus.isSubnormal_map_blockSU hker hδx i₀
  have hcIL : IsComponentOf ((TableBUE.blockSU (K := K) (n := f) IL).map φ)
      (φ.range ⊓ Subgroup.centralizer ({x} : Set G)) :=
    ⟨isSubnormal_le_of_assembly hsubIL, hsubIL,
      isQuasisimple_map_blockSU_of_two_le h hf hker hIL2⟩
  have hILL : (TableBUE.blockSU (K := K) (n := f) IL).map φ ≤ L := by
    rcases isComponentOf_le_or_commutator_eq_bot hcIL hLc.2.1 with h1 | h1
    · exact h1
    · exfalso
      apply commutator_ne_bot_of_isQuasisimple hLc.2.2
      rw [eq_bot_iff, ← h1]
      exact Subgroup.commutator_mono hLI le_rfl
  have hxst : δ x s = δ x t := hBst x hxB (δ x) (hδ x hxBs)
  have hmemIL : ∀ k, k ∈ IL ↔ δ x k = δ x i₀ := fun k => by
    rw [hIL, LinTorus.mem_diagClass]
    exact ⟨fun hk => hk x rfl, fun hk e he => by rw [Set.mem_singleton_iff.mp he]; exact hk⟩
  have hsIL : s ∈ IL := by
    by_contra hsn
    have htn : t ∉ IL := fun ht => hsn ((hmemIL s).mpr (hxst.trans ((hmemIL t).mp ht)))
    obtain ⟨ζ, hζo, hζq⟩ := CFSG.RankThree.Classical2.exists_orderOf_eq_norm_one h hp hpq
    set d : Fin (m + 1) → Kˣ := Pi.mulSingle s ζ * Pi.mulSingle t ζ⁻¹ with hd
    have hds : d s = ζ := by simp [hd, hst]
    have hdt : d t = ζ⁻¹ := by simp [hd, Ne.symm hst]
    have hdk : ∀ k, k ≠ s → k ≠ t → d k = 1 := fun k hks hkt => by simp [hd, hks, hkt]
    have hdcases : ∀ k, d k = 1 ∨ d k = ζ ∨ d k = ζ⁻¹ := by
      intro k
      by_cases hks : k = s
      · exact Or.inr (Or.inl (hks ▸ hds))
      by_cases hkt : k = t
      · exact Or.inr (Or.inr (hkt ▸ hdt))
      exact Or.inl (hdk k hks hkt)
    have hdn : ∀ k, d k ^ (2 ^ f + 1) = 1 := by
      intro k
      rcases hdcases k with hk | hk | hk <;> rw [hk]
      · exact one_pow _
      · exact hζq
      · rw [inv_pow, hζq, inv_one]
    have hdn' : ∀ k, (d k : K) ^ (2 ^ f + 1) = 1 := fun k => by
      rw [← Units.val_pow_eq_pow_val, hdn k, Units.val_one]
    have hdprod : ∏ k, d k = 1 := by
      simp only [hd, Pi.mul_apply, Finset.prod_mul_distrib, Fintype.prod_pi_mulSingle']
      exact mul_inv_cancel ζ
    have hdmem : diagHom (m + 1) d ∈ unitarySU 2 f K (m + 1) :=
      TableBUE.diagHom_mem_unitarySU h hdn hdprod
    set u : ↥(unitarySU 2 f K (m + 1)) := ⟨diagHom (m + 1) d, hdmem⟩ with hu
    have hdp : d ^ p = 1 := by
      funext k
      rw [Pi.pow_apply, Pi.one_apply]
      rcases hdcases k with hk | hk | hk <;> rw [hk]
      · exact one_pow _
      · rw [← hζo]; exact pow_orderOf_eq_one ζ
      · rw [inv_pow, ← hζo, pow_orderOf_eq_one ζ, inv_one]
    have hup : u ^ p = 1 := by
      apply Subtype.ext
      change (diagHom (m + 1) d) ^ p = 1
      rw [← map_pow, hdp, map_one]
    have hzBs : φ u ∈ Bs := SURep.mem_of_frame_inner hcfg.2.1 h hframe (d := u) (δ := d) rfl hup
    have hzact : SURep.GGFrameActs φ (φ u) d := SURep.frameActs_map φ rfl hdn'
    have hzL : φ u ∈ Subgroup.centralizer (L : Set G) := by
      refine Subgroup.centralizer_le hLI
        (SUTorus.mem_centralizer_map_blockSU (mem_suPairs_of_frameActs h hzact) ?_)
      intro i hi j hj
      have his : i ≠ s := fun h' => hsn (h' ▸ hi)
      have hit : i ≠ t := fun h' => htn (h' ▸ hi)
      have hjs : j ≠ s := fun h' => hsn (h' ▸ hj)
      have hjt : j ≠ t := fun h' => htn (h' ▸ hj)
      rw [hdk i his hit, hdk j hjs hjt]
    have hxL : x ∈ Subgroup.centralizer (L : Set G) :=
      mem_centralizer_of_le_centralizer hS.2.2.2.1.1
    set P := Bs ⊓ Subgroup.centralizer (L : Set G) with hP
    have hPp : IsPGroup p P := fun g => ⟨1, by
      rw [pow_one]
      exact Subtype.ext (hcfg.2.1.2.1.2 g.1 g.2.1)⟩
    have hPc : IsCyclic P := hS.2.2.2.2 P inf_le_right hPp
    have hzx : φ u ∈ Subgroup.zpowers x := mem_zpowers_of_isCyclic hp hPc ⟨hxBs, hxL⟩
      ⟨hzBs, hzL⟩ (hcfg.2.1.2.1.2 x hxBs) hS.2.2.1 (hcfg.2.1.2.1.2 _ hzBs)
    obtain ⟨k, hk⟩ := (mem_powers_iff_mem_zpowers.mpr hzx : φ u ∈ Submonoid.powers x)
    have hxk : SURep.GGFrameActs φ (φ u) (δ x ^ k) := hk ▸ (hδ x hxBs).pow h k
    have hr := SURep.ratio_eq_of_frameActs hkerU h hn hzact hxk s t
    rw [hds, hdt, Pi.pow_apply, Pi.pow_apply, hxst] at hr
    have hζ2 : ζ = ζ⁻¹ := mul_right_cancel hr
    have hζsq : ζ ^ 2 = 1 := by
      rw [sq]
      nth_rewrite 2 [hζ2]
      exact mul_inv_cancel ζ
    have h2 := orderOf_dvd_of_pow_eq_one hζsq
    rw [hζo] at h2
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2)
  have htIL : t ∈ IL := (hmemIL t).mpr (hxst.symm.trans ((hmemIL s).mp hsIL))
  set E := LinTorus.diagClass (D : Set G) δ s with hE
  have hsE : s ∈ E := LinTorus.self_mem_diagClass _ _ s
  have htE : t ∈ E := LinTorus.mem_diagClass.mpr fun e he =>
    (hBst e (hDB' he) (δ e) (hδ e (hBBs (hDB' he)))).symm
  have hEIL : E ⊆ IL := fun k hk =>
    (hmemIL k).mpr ((LinTorus.mem_diagClass.mp hk x hxD).trans ((hmemIL s).mp hsIL))
  have hE2 : 2 ≤ E.card := by
    have h1 : ({s, t} : Finset (Fin (m + 1))) ⊆ E := by
      intro k hk
      rcases Finset.mem_insert.mp hk with rfl | hk
      · exact hsE
      · rw [Finset.mem_singleton.mp hk]; exact htE
    have h2 := Finset.card_le_card h1
    rwa [Finset.card_pair hst] at h2
  have hBEL : (TableBUE.blockSU (K := K) (n := f) E).map φ ≤ L :=
    (Subgroup.map_mono (SUTorus.blockSU_mono hEIL)).trans hILL
  have hBEC : (TableBUE.blockSU (K := K) (n := f) E).map φ ≤
      Subgroup.centralizer (D : Set G) := by
    rw [← Subgroup.le_centralizer_iff]
    intro e he
    exact SUTorus.mem_centralizer_map_blockSU (hδD e he)
      fun i hi j hj => LinTorus.eq_of_mem_diagClass hi hj he
  have hsubE := SUTorus.isSubnormal_map_blockSU hker hδD s
  have hcE : IsComponentOf ((TableBUE.blockSU (K := K) (n := f) E).map φ)
      (φ.range ⊓ Subgroup.centralizer (D : Set G)) :=
    ⟨isSubnormal_le_of_assembly hsubE, hsubE, isQuasisimple_map_blockSU_of_two_le h hf hker hE2⟩
  have hcE' : IsComponentOf ((TableBUE.blockSU (K := K) (n := f) E).map φ)
      (L ⊓ Subgroup.centralizer (D : Set G)) :=
    CFSG.LocalAnalysis.ComponentInitial.isComponentOf_of_le hcE (le_inf hBEL hBEC)
      (inf_le_inf_right _ hLφ)
  have hBEJ : (TableBUE.blockSU (K := K) (n := f) E).map φ ≤ J := by
    rw [hcfg.2.2.1.2.2.2.2.1]
    exact le_sSup hcE'
  set τ := φ (SURep.swapU h s t) with hτ
  have hτJ : τ ∈ J := hBEJ (Subgroup.mem_map_of_mem φ (TableBUE.isBlockOn_permGL_swap hsE htE))
  have hτ1 : τ ≠ 1 := map_swapU_ne_one h hkerU hst
  have hτ2 : τ ^ 2 = 1 := by rw [hτ, pow_two, ← map_mul, swapU_mul_self, map_one]
  have hBτ : ∀ b ∈ B, b * τ * b⁻¹ = τ := by
    intro b hb
    rw [hτ, (hδ b (hBBs hb)).apply h,
      conjU_swapU_of_eq h _ (hBst b hb (δ b) (hδ b (hBBs hb)))]
  refine ggStdSubBstarCentralizer_of_twoSubgroup hcfg ⟨Subgroup.zpowers τ, ?_, ?_,
    Subgroup.zpowers_le.mpr hτJ, fun b hb => ?_⟩
  · intro hT
    have h1 := Subgroup.mem_zpowers τ
    rw [hT, Subgroup.mem_bot] at h1
    exact hτ1 h1
  · exact IsPGroup.of_card (n := 1)
      (by rw [Nat.card_zpowers, orderOf_eq_prime hτ2 hτ1, pow_one])
  · refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun y hy => ?_)
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    have hc : Commute b τ := by
      have h1 := hBτ b hb
      calc b * τ = b * τ * b⁻¹ * b := by group
        _ = τ * b := by rw [h1]
    exact (hc.zpow_right k).eq.symm

end Core

end SURepair

section Inputs

@[expose] def GGUnitaryBFramePairInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (n f : ℕ) (ψ : (ggU .PSU n (f + 1)).K →* G),
    GGSixCtxV2 p B Bs x L D J (ggU .PSU n (f + 1)).D .PSU n (f + 1) ψ →
      GGSixStepOne p B Bs x L D J → p ∣ 2 ^ (f + 1) + 1 →
        ∀ (P : GL (Fin n) (GaloisField 2 (2 * (f + 1))))
          (hP : conjTr (unitaryInvolution (GaloisField 2 (2 * (f + 1))) 2 (f + 1))
            (P : Matrix (Fin n) (Fin n) (GaloisField 2 (2 * (f + 1)))) *
              (P : Matrix (Fin n) (Fin n) (GaloisField 2 (2 * (f + 1)))) = antidiag n),
          (∀ b ∈ Bs, SURep.GGFrameDiagU (SURep.ggFrameU
            (card_galoisField_two_mul 2 (f + 1) (Nat.le_add_left 1 f)) ψ P hP) b) →
          B = Bs ∨ ∃ s t : Fin n, s ≠ t ∧ SURepair.GGFramePair (SURep.ggFrameU
            (card_galoisField_two_mul 2 (f + 1) (Nat.le_add_left 1 f)) ψ P hP) B s t

theorem ggUnitaryBstarCentralizerInput_of_pair (hTB : GGUnitaryBFramePairInput) :
    GGUnitaryBstarCentralizerInput := by
  intro G _ _ p B Bs x L D J n f ψ hctx s1 hp hf2
  obtain ⟨f, rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
  have hrank : 2 ≤ n / 2 := hctx.2.2.2.1.2
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨P, hP, hframe⟩ := ggSUBstarFrameInput_holds G p B Bs x L D J (m + 1) f ψ hctx s1 hp
  have hF : Nat.card (GaloisField 2 (2 * (f + 1))) = (2 ^ (f + 1)) ^ 2 :=
    card_galoisField_two_mul 2 (f + 1) (Nat.le_add_left 1 f)
  have h : UnitaryFieldData 2 (f + 1) (GaloisField 2 (2 * (f + 1))) :=
    ⟨Nat.prime_two, by omega, by rw [hF, ← pow_mul, mul_comm]⟩
  obtain ⟨hrange, hker⟩ := hctx.2.2.2.2.1
  have hrφ : (SURep.ggFrameU hF ψ P hP).range = ggG0 p B x L D J :=
    (SURep.range_ggFrameU hF ψ P hP).trans hrange
  exact SURepair.bstar_inf_centralizer_le_of_pair h hf2 (by omega)
    ⟨hctx.1, hctx.2.1, hctx.2.2.1⟩ hp (SURep.ker_ggFrameU_le hF ψ P hP hker)
    (by rw [hrφ]; exact le_sup_left) hframe
    (hTB G p B Bs x L D J (m + 1) f ψ hctx s1 hp P hP hframe)

theorem ggStepTwoUnitaryFusionLargeInput_of_pair (hTB : GGUnitaryBFramePairInput) :
    GGStepTwoUnitaryFusionLargeInput :=
  ggStepTwoUnitaryFusionLargeInput_of_centralizer (ggUnitaryBstarCentralizerInput_of_pair hTB)

end Inputs

end CFSG.StandardType
