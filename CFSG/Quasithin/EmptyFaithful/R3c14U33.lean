module

public import CFSG.Quasithin.EmptyFaithful.R3c14Cfg
public import CFSG.Quasithin.Recognition.CertU33AutBound
public import CFSG.Timmesfeld.Final.PSU33
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTightEmbeddingAction
public import CFSG.LocalAnalysis.ComponentClassification.BlockMutualRanks
public import CFSG.LocalAnalysis.ComponentClassification.BlockTwoProductAction
public import CFSG.LocalAnalysis.ComponentClassification.InvolutionGeneratedSubgroup
public import CFSG.LocalAnalysis.ComponentClassification.OrbitBlockConjugation
public import CFSG.LocalAnalysis.ComponentClassification.SylowTwoImageLifting
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionFixedInvolution
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionProperEmbedding
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListAlt7
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKAbs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKCover
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKDefs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKQuot
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23FiveDefs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InA3Five
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_20
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_8Aut
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Quasithin.Background.A1cA132Action
public import CFSG.Quasithin.Background.A1cA133Three
public import CFSG.Quasithin.Background.B1More13A
public import CFSG.Quasithin.Background.B1More13Defs
public import CFSG.Quasithin.Background.B1MoreEleven
public import CFSG.Quasithin.Background.B5CompA
public import CFSG.Quasithin.Background.B5CompB
public import CFSG.Quasithin.Background.D2
public import CFSG.Quasithin.Background.D2Dihedral
public import CFSG.Quasithin.Background.E3
public import CFSG.Quasithin.Background.E3Nprime
public import CFSG.Quasithin.Background.E3OffenderB
public import CFSG.Quasithin.Background.E3Uniq
public import CFSG.Quasithin.Background.E4Solv
public import CFSG.Quasithin.Background.GoldschmidtS146RBend1
public import CFSG.Quasithin.Background.ThreePrimeGroup
public import CFSG.Quasithin.EmptyFaithful.R3c12Syl
public import CFSG.Quasithin.EmptyFaithful.R3c2List
public import CFSG.Quasithin.EmptyFaithful.S14110
public import CFSG.Quasithin.EmptyFaithful.S1469Inputs
public import CFSG.Quasithin.EmptyFaithful.S1469Sev
public import CFSG.Quasithin.EmptyFaithful.S146F4
public import CFSG.Quasithin.EmptyFaithful.S146yBorel
public import CFSG.Quasithin.EmptyFaithful.S151Basic
public import CFSG.Quasithin.EmptyFaithful.S153D25
public import CFSG.Quasithin.EmptyFaithful.S153D43
public import CFSG.Quasithin.EmptyFaithful.S153Nine
public import CFSG.Sporadic.Schreier.J4SSylow
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82Orbit
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Lemma115Torus
public import CFSG.Timmesfeld.Moufang.Three
public import CFSG.Timmesfeld.RankOne
public import CFSG.Timmesfeld.Special.TwoCore

public section

namespace CFSG.Quasithin.R3c14

open CFSG.Quasithin CFSG.QuasithinUnique

section U33

set_option maxRecDepth 100000 in
theorem y_cands : ∀ iy : ℕ, iy < 160 →
    autRelY (u33GenTab.getD 0 []) (u33GenTab.getD 1 []) (u33GenTab.getD 2 [])
      (u33ABTab.getD iy []) = true → u33ABTab.getD iy [] = u33GenTab.getD 4 [] := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem tel_central_comm_y : ∀ i : ℕ, i < 32 →
    compL (u33TelTab.getD i []) (u33GenTab.getD 0 []) =
      compL (u33GenTab.getD 0 []) (u33TelTab.getD i []) →
    compL (u33TelTab.getD i []) (u33GenTab.getD 1 []) =
      compL (u33GenTab.getD 1 []) (u33TelTab.getD i []) →
    compL (u33TelTab.getD i []) (u33GenTab.getD 2 []) =
      compL (u33GenTab.getD 2 []) (u33TelTab.getD i []) →
    compL (u33TelTab.getD i []) (u33GenTab.getD 4 []) =
      compL (u33GenTab.getD 4 []) (u33TelTab.getD i []) := by
  decide +kernel

theorem permL_gen (k : ℕ) (hk : k < 5) :
    permL (u33PresHom (u33GenPG k)) = u33GenTab.getD k [] := by
  rw [u33PresHom_genPG, u33_genTab_eq k hk]

theorem permL_comm_of_comm {g h : U33G} (hc : g * h = h * g) :
    compL (permL (u33PresHom g)) (permL (u33PresHom h)) =
      compL (permL (u33PresHom h)) (permL (u33PresHom g)) := by
  rw [compL_permL, compL_permL, ← map_mul, ← map_mul, hc]

theorem comm_of_permL_comm
    {g h : U33G}
    (hc : compL (permL (u33PresHom g)) (permL (u33PresHom h)) =
      compL (permL (u33PresHom h)) (permL (u33PresHom g))) : g * h = h * g := by
  rw [compL_permL, compL_permL, permL_eq_iff, ← map_mul, ← map_mul] at hc
  exact u33PresHom_injective hc

theorem central_comm_y
    {v : U33G} (hv : v ∈ u33Data.T) (hc : ∀ t ∈ u33Data.T, t * v = v * t) :
    v * u33GenPG 4 = u33GenPG 4 * v := by
  obtain ⟨i, rfl⟩ := (u33Data.mem_T_iff v).mp hv
  have hi : permL (u33PresHom (u33Data.Tel i)) = u33TelTab.getD i [] := permL_Tel i
  have key : ∀ k, k < 3 → compL (u33TelTab.getD i []) (u33GenTab.getD k []) =
      compL (u33GenTab.getD k []) (u33TelTab.getD i []) := by
    intro k hk
    have hgT : u33GenPG k ∈ u33Data.T := by
      interval_cases k
      · exact u33Data.a_mem_T
      · exact u33Data.b_mem_T
      · exact u33Data.s_mem_T
    have := permL_comm_of_comm (hc _ hgT)
    rw [permL_gen k (by omega), hi] at this
    exact this.symm
  have := tel_central_comm_y i i.2 (key 0 (by norm_num)) (key 1 (by norm_num))
    (key 2 (by norm_num))
  apply comm_of_permL_comm
  rw [← hi, permL_gen 4 (by norm_num)] at *
  exact this

theorem eq_one_of_fixes_A
    {φ : MulAut U33G} (hT : ∀ t ∈ u33Data.T, φ t = t)
    (hx : φ (u33GenPG 3) = u33GenPG 3) : φ = 1 := by
  have hmap : Subgroup.map φ.toMonoidHom u33Data.T = u33Data.T := by
    ext z
    constructor
    · rintro ⟨t, ht, rfl⟩
      show φ t ∈ u33Data.T
      rw [hT t ht]
      exact ht
    · intro hz
      exact ⟨z, hz, hT z hz⟩
  have ha : φ (u33GenPG 0) = u33GenPG 0 := hT _ u33Data.a_mem_T
  have hb : φ (u33GenPG 1) = u33GenPG 1 := hT _ u33Data.b_mem_T
  have hs : φ (u33GenPG 2) = u33GenPG 2 := hT _ u33Data.s_mem_T
  have hy : φ (u33GenPG 4) = u33GenPG 4 := by
    obtain ⟨iy, hiy, hyi⟩ := exists_index_AB (map_mem_AB_of_map_T hmap (Or.inr u33Data.y_mem_B))
    have R := u33G_rels_map (u33PresHom.comp φ.toMonoidHom)
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom] at R
    obtain ⟨-, -, ⟨r11, r12, r13, r14⟩⟩ := R
    simp only [ha, hb, hs] at r12 r13 r14
    have hrel := autRelY_permL.2 ⟨r11, r12, r13, r14⟩
    rw [permL_gen 0 (by norm_num), permL_gen 1 (by norm_num), permL_gen 2 (by norm_num)] at hrel
    have hyi' : permL (u33PresHom (φ (u33GenPG 4))) = u33ABTab.getD iy [] := hyi
    rw [hyi'] at hrel
    have h4 := y_cands iy hiy hrel
    have : permL (u33PresHom (φ (u33GenPG 4))) = permL (u33PresHom (u33GenPG 4)) := by
      rw [hyi', h4, permL_gen 4 (by norm_num)]
    exact u33PresHom_injective (permL_eq_iff.mp this)
  have hgen : ∀ g ∈ ({u33GenPG 0, u33GenPG 1, u33GenPG 2, u33GenPG 3, u33GenPG 4} : Set U33G),
      φ.toMonoidHom g = (MonoidHom.id U33G) g := by
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl
    exacts [ha, hb, hs, hx, hy]
  ext g
  have hg : g ∈ Subgroup.closure
      ({u33GenPG 0, u33GenPG 1, u33GenPG 2, u33GenPG 3, u33GenPG 4} : Set U33G) := by
    rw [u33_gen]
    trivial
  exact MonoidHom.eqOn_closure hgen hg

theorem not_elData
    {V H : Subgroup U33G} {ζ : MulAut U33G}
    (h : ElData u33Data.T V H ζ) : False := by
  classical
  have : Finite U33G := u33Pres_finite_card_le.1
  have hfixK : ∀ k ∈ u33Data.T ⊔ H, ζ k = k := by
    have hle : u33Data.T ⊔ H ≤ MonoidHom.eqLocus ζ.toMonoidHom (MonoidHom.id U33G) :=
      sup_le (fun t ht => h.fixT t ht) (fun k hk => h.fixH k hk)
    exact fun k hk => hle hk
  obtain ⟨y, hyH, hy3, hyn⟩ := h.y3
  have hyK : y ∈ u33Data.T ⊔ H := Subgroup.mem_sup_right hyH
  rcases u33Data.lattice (u33Data.T ⊔ H) le_sup_left with hKT | hKA | hKB | hKtop
  ·
    have hyT : y ∈ u33Data.T := hKT ▸ hyK
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp u33_syl.1) (⟨y, hyT⟩ : ↥u33Data.T)
    have hk' : orderOf y = 2 ^ k := (Subgroup.orderOf_coe (⟨y, hyT⟩ : ↥u33Data.T)).trans hk
    have hdvd : 2 ^ k ∣ 3 := by
      rw [← hk']
      exact orderOf_dvd_of_pow_eq_one hy3
    have hk0 : 2 ^ k = 1 :=
      (Nat.Coprime.pow_left k (by norm_num : Nat.Coprime 2 3)).eq_one_of_dvd hdvd
    rw [hk0, orderOf_eq_one_iff] at hk'
    exact hyn fun v _ => by rw [hk', one_mul, mul_one]
  ·
    apply h.ne
    refine eq_one_of_fixes_A h.fixT ?_
    exact hfixK _ (hKA ▸ u33Data.x_mem_A)
  ·
    have hVT : V ≤ u33Data.T := h.VT
    have hVn : (V.subgroupOf u33Data.T).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hVT).mpr h.TV
    have hV1 : V.subgroupOf u33Data.T ≠ ⊥ := by
      intro hb
      have h1 : Nat.card (V.subgroupOf u33Data.T) = 1 := by rw [hb]; exact Subgroup.card_bot
      have h2 : Nat.card (V.subgroupOf u33Data.T) = Nat.card V :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVT).toEquiv
      have := h.V4
      omega
    have hnil : Group.IsNilpotent ↥u33Data.T := u33_syl.1.isNilpotent
    have hcen := Group.IsNilpotent.inf_center_ne_bot_of_normal hV1
    obtain ⟨⟨⟨v, hvT⟩, hvmem⟩, hv1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hcen
    have hvV : v ∈ V := Subgroup.mem_subgroupOf.mp hvmem.1
    have hvc : ∀ t ∈ u33Data.T, t * v = v * t := fun t ht => by
      have := Subgroup.mem_center_iff.mp hvmem.2 ⟨t, ht⟩
      exact congrArg Subtype.val this
    have hvy := central_comm_y hvT hvc
    have hBc : u33Data.B ≤ Subgroup.centralizer ({v} : Set U33G) := by
      unfold OvergroupData.B
      rw [Subgroup.closure_le]
      intro g hg
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      rcases hg with rfl | rfl | rfl | rfl
      · exact hvc _ u33Data.a_mem_T
      · exact hvc _ u33Data.b_mem_T
      · exact hvc _ u33Data.s_mem_T
      · exact hvy.symm
    have hHB : H ≤ u33Data.B := hKB ▸ le_sup_right
    have hv1' : v = 1 := h.fix v hvV fun k hk => by
      exact Subgroup.mem_centralizer_singleton_iff.mp (hBc (hHB hk))
    exact hv1 (Subtype.ext (Subtype.ext hv1'))
  ·
    apply h.ne
    ext g
    exact hfixK g (hKtop ▸ Subgroup.mem_top g)

end U33

section Main

theorem not_elConfig_u33G :
    ¬ ElConfig U33G := by
  intro hc
  have : Finite U33G := u33Pres_finite_card_le.1
  have hsyl : IsSylowTwoOf u33Data.T ⊤ := K1.isSylowTwoOf_top_iff.mpr u33_syl
  obtain ⟨V, H, ζ, hd⟩ := ElConfig.of_sylow hsyl hc
  exact not_elData hd

theorem not_elConfig_of_u33
    {X : Type} [Group X]
    (h : CFSG.Assembly.LowTwoRank.StatedClassicalModel X .PSU 3 3 1) : ¬ ElConfig X := by
  intro hc
  obtain ⟨e₁⟩ := CFSG.Timmesfeld.nonempty_mulEquiv_PSU3_of_lieModel
    (Or.inl ⟨by decide, h⟩ : CFSG.Blueprint.LieModel X .PSU 3 3 1)
  obtain ⟨e₂⟩ := u33Pres_mulEquiv_PSU3
  exact not_elConfig_u33G (ElConfig.map (e₁.trans e₂.symm) hc)

end Main

end CFSG.Quasithin.R3c14
