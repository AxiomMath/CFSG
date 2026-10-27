module

public import CFSG.Quasithin.EmptyFaithful.S14112

public section

namespace CFSG.Quasithin

open CFSG.Open

variable {G : Type} [Group G] [Finite G]

section RankTwo

private theorem s14118_card_mulAut_le_six {V : Type*} [Group V] [Finite V]
    (hV : Nat.card V = 4) : Nat.card (MulAut V) ≤ 6 ∧ Finite (MulAut V) := by
  classical
  let f : MulAut V → Equiv.Perm {v : V // v ≠ 1} := fun a =>
    Equiv.Perm.subtypePerm a.toEquiv (by intro v; simp)
  have hf : Function.Injective f := by
    intro a b hab
    ext v
    by_cases hv : v = 1
    · simp [hv]
    · exact congrArg Subtype.val (DFunLike.congr_fun hab ⟨v, hv⟩)
  have : Fintype V := Fintype.ofFinite V
  have hthree : Nat.card {v : V // v ≠ 1} = 3 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl]
    have hone : Fintype.card {v : V // v = 1} = 1 := by simp
    rw [hone, ← Nat.card_eq_fintype_card, hV]
  refine ⟨?_, Finite.of_injective f hf⟩
  calc Nat.card (MulAut V) ≤ Nat.card (Equiv.Perm {v : V // v ≠ 1}) :=
        Nat.card_le_card_of_injective f hf
    _ = 6 := by rw [Nat.card_perm, hthree]; rfl

omit [Finite G] in
private theorem s14118_conjAct_coe (V : Subgroup G) (g : Subgroup.normalizer (V : Set G))
    (x : V) : ((conjAct V g x : V) : G) = g * x * (g : G)⁻¹ :=
  CFSG.Quasithin.AutOn.coe_conjAct_apply V g x

omit [Finite G] in
private theorem s14118_conjAct_eq_one_iff {V : Subgroup G} {g : Subgroup.normalizer (V : Set G)} :
    conjAct V g = 1 ↔ (g : G) ∈ Subgroup.centralizer (V : Set G) :=
  CFSG.Quasithin.AutOn.conjAct_eq_one_iff g

omit [Finite G] in
theorem quasithinOmegaOneCenter_le_center (T : Subgroup G) :
    quasithinOmegaOneCenter T ≤ T ⊓ Subgroup.centralizer (T : Set G) :=
  (Subgroup.closure_le _).mpr fun _ hz => hz.1

private theorem s14118_isTwoReducedIn {T Mc M : Subgroup G} (h : quasithinQTFE14Cat G T Mc)
    (hM : InM T M) : IsTwoReducedIn M (VZ T M) ∧ VZ T M ≤ T := by
  obtain ⟨S, hS⟩ := h.exists_sylow
  have hSM : (S : Subgroup G) ≤ M := hS ▸ hM.2
  have hF : M ⊓ Subgroup.centralizer (pCoreOf 2 M : Set G) ≤ pCoreOf 2 M :=
    h.qtke.2.1 M hM.1.1 ⟨S, hSM⟩
  have hVred : IsTwoReducedIn M (VZ T M) := by
    have := isTwoReducedIn_conjClosure M S hSM hF le_rfl
    rwa [hS] at this
  refine ⟨hVred, ?_⟩
  have := le_sylow_of_isTwoReducedIn S hSM hVred
  rwa [hS] at this

theorem eq_mc_of_le_centralizer_VZ {T Mc M : Subgroup G} (h : quasithinQTFE14Cat G T Mc)
    (hM : InM T M) (hTV : T ≤ Subgroup.centralizer (VZ T M : Set G)) : M = Mc := by
  obtain ⟨hVred, hVT⟩ := s14118_isTwoReducedIn h hM
  have hVZ : VZ T M ≤ quasithinOmegaOneCenter T := by
    intro v hv
    apply Subgroup.subset_closure
    refine ⟨⟨hVT hv, Subgroup.mem_centralizer_iff.mpr fun t ht => ?_⟩, hVred.2.2.1.2 v hv⟩
    exact ((Subgroup.mem_centralizer_iff.mp (hTV ht)) v hv).symm
  have hVeq : VZ T M = quasithinOmegaOneCenter T := le_antisymm hVZ (le_conjClosure _ _)
  have hZ2 : IsPGroup 2 (quasithinOmegaOneCenter T) :=
    h.sylow.1.to_le ((quasithinOmegaOneCenter_le_center T).trans inf_le_left)
  have hMN : M ≤ Subgroup.normalizer (quasithinOmegaOneCenter T : Set G) := hVeq ▸ hVred.2.1
  have hNM : Subgroup.normalizer (quasithinOmegaOneCenter T : Set G) = M :=
    hM.1.2 _ ⟨_, h.omegaOneCenter_ne_bot, hZ2, rfl⟩ hMN
  have hCM : Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) ≤ M :=
    hNM ▸ Subgroup.centralizer_le_normalizer _
  exact h.mc_unique M hM.1 hCM

theorem autOn_eq_top_of_card_VZ_eq_four {T Mc M : Subgroup G} (h : quasithinQTFE14Cat G T Mc)
    (hM : InM T M) (hne : M ≠ Mc) (h4 : Nat.card (VZ T M) = 4) : autOn M (VZ T M) = ⊤ := by
  obtain ⟨hVred, -⟩ := s14118_isTwoReducedIn h hM
  have hnot : ¬ T ≤ Subgroup.centralizer (VZ T M : Set G) := fun hTV =>
    hne (eq_mc_of_le_centralizer_VZ h hM hTV)
  obtain ⟨hcard6, hfin⟩ := s14118_card_mulAut_le_six h4
  obtain ⟨t, htT, htC⟩ := IsConcreteLE.not_le_iff_exists.mp hnot
  have htN : t ∈ Subgroup.normalizer (VZ T M : Set G) := hVred.2.1 (hM.2 htT)
  have ha : conjAct (VZ T M) ⟨t, htN⟩ ∈ autOn M (VZ T M) :=
    ⟨⟨t, htN⟩, Subgroup.mem_subgroupOf.mpr (hM.2 htT), rfl⟩
  have ha1 : conjAct (VZ T M) ⟨t, htN⟩ ≠ 1 := fun h1 => htC (s14118_conjAct_eq_one_iff.mp h1)
  obtain ⟨k, hk⟩ := h.sylow.1 ⟨t, htT⟩
  have hak : conjAct (VZ T M) ⟨t, htN⟩ ^ 2 ^ k = 1 := by
    have hpow : (⟨t, htN⟩ : Subgroup.normalizer (VZ T M : Set G)) ^ 2 ^ k = 1 := by
      apply Subtype.ext
      simpa using congrArg Subtype.val hk
    rw [← map_pow, hpow, map_one]
  have h2dvd : 2 ∣ Nat.card (autOn M (VZ T M)) := by
    have hord := Subgroup.orderOf_dvd_natCard _ ha
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hak)
    have hj0 : j ≠ 0 := by
      rintro rfl
      exact ha1 (orderOf_eq_one_iff.mp (by simpa using hj))
    rw [hj] at hord
    exact (dvd_pow_self 2 hj0).trans hord
  have hnot2 : ¬ IsPGroup 2 (autOn M (VZ T M)) := by
    intro hp
    apply hnot
    refine hM.2.trans (hVred.2.2.2 M le_rfl Subgroup.le_normalizer fun d hd => ?_)
    have hdN : d ∈ Subgroup.normalizer (VZ T M : Set G) := hVred.2.1 hd
    obtain ⟨k, hk⟩ := hp ⟨conjAct (VZ T M) ⟨d, hdN⟩,
      ⟨⟨d, hdN⟩, Subgroup.mem_subgroupOf.mpr hd, rfl⟩⟩
    refine ⟨k, ?_⟩
    have hk' : conjAct (VZ T M) ⟨d, hdN⟩ ^ 2 ^ k = 1 := by
      simpa using congrArg Subtype.val hk
    have hdk : d ^ 2 ^ k ∈ Subgroup.normalizer (VZ T M : Set G) := pow_mem hdN _
    have heq : (⟨d ^ 2 ^ k, hdk⟩ : Subgroup.normalizer (VZ T M : Set G)) =
        ⟨d, hdN⟩ ^ 2 ^ k := Subtype.ext (by simp)
    have h1 : conjAct (VZ T M) ⟨d ^ 2 ^ k, hdk⟩ = 1 := by
      rw [heq, map_pow, hk']
    exact s14118_conjAct_eq_one_iff.mp h1
  have hle : Nat.card (autOn M (VZ T M)) ≤ Nat.card (MulAut (VZ T M)) :=
    Subgroup.card_le_card_group _
  have hne2 : Nat.card (autOn M (VZ T M)) ≠ 2 := fun h2 =>
    hnot2 (IsPGroup.of_card (n := 1) (by rw [h2]; rfl))
  have hne4 : Nat.card (autOn M (VZ T M)) ≠ 4 := fun h4' =>
    hnot2 (IsPGroup.of_card (n := 2) (by rw [h4']; rfl))
  have hpos : 0 < Nat.card (autOn M (VZ T M)) := Nat.card_pos
  exact Subgroup.eq_top_of_le_card _ (by omega)

theorem card_le_two_of_le_of_ne_of_card_four {W V : Subgroup G} (hWV : W ≤ V) (hW : W ≠ V)
    (h4 : Nat.card V = 4) : Nat.card W ≤ 2 := by
  have hd : Nat.card W ∣ 2 ^ 2 := by
    rw [show (2 : ℕ) ^ 2 = 4 by norm_num, ← h4]
    exact Subgroup.card_dvd_of_le hWV
  obtain ⟨j, hj, hj'⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
  interval_cases j
  · rw [hj']; norm_num
  · rw [hj']; norm_num
  · exact absurd (Subgroup.eq_of_le_of_card_ge hWV (by rw [h4, hj']; norm_num)) hW

theorem card_omegaOneCenter_eq_two_of_card_VZ_eq_four {T Mc M : Subgroup G}
    (h : quasithinQTFE14Cat G T Mc) (hM : InM T M) (hne : M ≠ Mc) (h4 : Nat.card (VZ T M) = 4) :
    Nat.card (quasithinOmegaOneCenter T) = 2 := by
  have hnot : ¬ T ≤ Subgroup.centralizer (VZ T M : Set G) := fun hTV =>
    hne (eq_mc_of_le_centralizer_VZ h hM hTV)
  have hZW : quasithinOmegaOneCenter T ≤ VZ T M ⊓ Subgroup.centralizer (T : Set G) :=
    le_inf (le_conjClosure _ _) ((quasithinOmegaOneCenter_le_center T).trans inf_le_right)
  have hWne : VZ T M ⊓ Subgroup.centralizer (T : Set G) ≠ VZ T M := by
    intro hWV
    apply hnot
    intro t ht
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have hv' : v ∈ VZ T M ⊓ Subgroup.centralizer (T : Set G) := by
      rw [hWV]
      exact hv
    exact ((Subgroup.mem_centralizer_iff.mp hv'.2) t ht).symm
  have hW2 := card_le_two_of_le_of_ne_of_card_four inf_le_left hWne h4
  have hZdvd := Subgroup.card_dvd_of_le hZW
  have hZ1 : Nat.card (quasithinOmegaOneCenter T) ≠ 1 := fun h1 =>
    h.omegaOneCenter_ne_bot (Subgroup.card_eq_one.mp h1)
  have hWpos : 0 < Nat.card ↥(VZ T M ⊓ Subgroup.centralizer (T : Set G)) := Nat.card_pos
  have hZpos : 0 < Nat.card (quasithinOmegaOneCenter T) := Nat.card_pos
  have := Nat.le_of_dvd hWpos hZdvd
  omega

theorem ordLE_mc_of_card_two {T Mc M : Subgroup G} (h : quasithinQTFE14Cat G T Mc)
    (h11 : ∃ C₂ : Subgroup G, Lemma14111Concl T Mc C₂) (hM : IsMf T Mc M)
    (hZ : Nat.card (quasithinOmegaOneCenter T) = 2) : OrdLE T Mc M := by
  obtain ⟨C₂, hC⟩ := h11
  have hC₂p : IsPGroup 2 C₂ := h.sylow.1.to_le (hC.2.1.trans inf_le_left)
  obtain ⟨Mf, hMf, hNMf⟩ :=
    exists_maxTwoLocal_ge (L := Subgroup.normalizer (C₂ : Set G)) ⟨C₂, hC.1, hC₂p, rfl⟩
  have hMfIs : IsMf T Mc Mf := isMf_of_lemma14111Concl h hC hMf hNMf
  have hMfeq : Mf = M := hM.1.2 Mf hMfIs.1.1 (hMfIs.2.2 M hM.1.1 hM.2.1)
  rcases hC.2.2.2 Mc h.inM_mc with hfac | ⟨-, hlt⟩
  · rw [← hMfeq]
    exact ordLE_of_factorization hfac hNMf
  · omega

omit [Finite G] in
theorem normalizer_le_centralizer_of_card_two {Z : Subgroup G} (hZ : Nat.card Z = 2) :
    Subgroup.normalizer (Z : Set G) ≤ Subgroup.centralizer (Z : Set G) := by
  intro g hg
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  by_cases hz1 : z = 1
  · rw [hz1, one_mul, mul_one]
  have hgz : g * z * g⁻¹ ∈ Z := (Subgroup.mem_normalizer_iff.mp hg z).mp hz
  obtain ⟨y, -, hy⟩ := (Nat.card_eq_two_iff' (1 : Z)).mp hZ
  have hgz1 : (⟨g * z * g⁻¹, hgz⟩ : Z) ≠ 1 := by
    intro h1
    apply hz1
    have := congrArg Subtype.val h1
    simpa using this
  have h1 := hy ⟨z, hz⟩ (fun h1 => hz1 (congrArg Subtype.val h1))
  have h2 := hy _ hgz1
  have h3 : g * z * g⁻¹ = z := congrArg Subtype.val (h2.trans h1.symm)
  calc z * g = (g * z * g⁻¹) * g := by rw [h3]
    _ = g * z := by group

theorem mc_eq_centralizer_of_card_two {T Mc M : Subgroup G} (h : quasithinQTFE14Cat G T Mc)
    (hM : IsMf T Mc M) (h4 : Nat.card (VZ T M) = 4)
    (hZ : Nat.card (quasithinOmegaOneCenter T) = 2) (hle : OrdLE T Mc M) :
    Mc = Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) := by
  obtain ⟨S, hS⟩ := h.exists_sylow
  have hv : ∀ K, InM T K → IsHv T K := fun K hK => by
    have := isHv_of_inM h.qtke.2.1 S (hS ▸ hK)
    rwa [hS] at this
  have hVle : VZ T Mc ≤ VZ T M := VZ_le_of_ordLE hle
  have hVne : VZ T Mc ≠ VZ T M := fun heq =>
    hM.2.1 (eq_of_VZ_eq (hv M hM.1.1) (hv Mc h.inM_mc) heq.symm)
  have hcard := card_le_two_of_le_of_ne_of_card_four hVle hVne h4
  have hVZ : quasithinOmegaOneCenter T = VZ T Mc :=
    Subgroup.eq_of_le_of_card_ge (le_conjClosure _ _) (by rw [hZ]; exact hcard)
  have hMcN : Mc ≤ Subgroup.normalizer (quasithinOmegaOneCenter T : Set G) :=
    hVZ ▸ le_normalizer_conjClosure _ _
  exact le_antisymm (hMcN.trans (normalizer_le_centralizer_of_card_two hZ)) h.centralizer_le_mc

end RankTwo

theorem stageRankTwoHyp1421_of_stageLemma14111 (h11 : StageLemma14111) :
    StageRankTwoHyp1421 := by
  intro G _ _ T Mc M h hM h4
  have hne : M ≠ Mc := hM.2.1
  have hZ := card_omegaOneCenter_eq_two_of_card_VZ_eq_four h hM.1.1 hne h4
  have hle := ordLE_mc_of_card_two h (h11 G T Mc h) hM hZ
  have hMc := mc_eq_centralizer_of_card_two h hM h4 hZ hle
  exact
    { simple := h.simple
      nonabelian := h.nonabelian
      qtke := h.qtke
      sylow := h.sylow
      faithful_empty := h.faithful_empty
      mc_max := hMc ▸ h.mc_max
      m_max := hM.1
      m_greatest := fun M' hM' => by
        by_cases hc : M' = Mc
        · rw [hc]
          exact hle
        · exact hM.2.2 M' hM' hc
      rank_two := h4
      aut_top := autOn_eq_top_of_card_VZ_eq_four h hM.1.1 hne h4
      two_maximal := ⟨Mc, h.inM_mc, hne.symm⟩ }

end CFSG.Quasithin
