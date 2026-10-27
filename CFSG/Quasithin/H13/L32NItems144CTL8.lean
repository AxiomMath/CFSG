module

public import CFSG.Quasithin.H13.L32NItems144CTL7
public import CFSG.Quasithin.Background.B2FactorizationR2
public import CFSG.Quasithin.H13.L32NItems144CTL1

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.LieType.BorelTits

namespace L1444CTL

open L1444

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem card_quot_le {K : Subgroup G}
    (hK : Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 5)) ∨
      LieModel (↥K ⧸ CFSG.pCore 2 ↥K) .PSL 3 2 1) :
    Nat.card (OTwoQuot K) ≤ 168 := by
  have e := QuotientGroup.quotientMulEquivOfEq (CFSG.pCore_eq_open (↥K) 2)
  calc Nat.card (OTwoQuot K) = Nat.card (↥K ⧸ CFSG.pCore 2 ↥K) :=
        (Nat.card_congr e.toEquiv).symm
    _ ≤ 168 := by
      rcases hK with hK | h3
      · obtain ⟨f⟩ := hK
        rw [Nat.card_congr f.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
          Fintype.card_fin]
        decide
      · obtain ⟨f⟩ := nonempty_equiv_SL32_of_lieModel h3
        rw [Nat.card_congr f.toEquiv, HSType.card_SL_three_two]

section Setup

variable {T L V V₂ : Subgroup G} {g : G} {D : HatModelU (fsuU T V)} {Q₁ Q₂ : Subgroup G}
  (S : Setup4 G T L V V₂ g D Q₁ Q₂)
include S

theorem z_mem_V1 : S.cfg.z ∈ fsuV1 T V := by
  have hzZ : S.cfg.z ∈ centerOf (fsuU T V) := S.mem_center_iff.mpr (Or.inr rfl)
  rwa [S.zU] at hzZ

theorem z_not_mem_centralizer (h12213 : Stmt12_2_13) (h13322 : Stmt13_3_2_two)
    (hV : StmtL32NModule) : S.cfg.z ∉ Subgroup.centralizer (L : Set G) := by
  intro hz
  have hV1T : fsuV1 T V ≤ T := fun v hv => S.QT (S.U_le_Q (V_le_U hv.1))
  have hV1 : fsuV1 T V ≠ ⊥ := fun h => by
    have h2 := S.card2
    rw [h, Subgroup.card_bot] at h2
    omega
  have hL : L ≤ Subgroup.normalizer (fsuV1 T V : Set G) := fun l hl =>
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun v hv => by
      have hv' : v ∈ centerOf (fsuU T V) := by rwa [S.zU]
      rcases S.mem_center_iff.mp hv' with rfl | rfl
      · simp
      · exact (Subgroup.mem_centralizer_iff.mp hz l hl).symm)
  exact lemma12_8_3_four h12213 (S.hyp.hyp1281One h13322 hV) (S.hyp.isTSub_fsuV1 hV)
    (normalizer_le_M S h13322 hV1 (S.hyp.fsu.sylow.1.to_le hV1T) (sup_le hL S.TH))

theorem comm_z {h : G} (hhH : h ∈ l32nH T V) : h * S.cfg.z = S.cfg.z * h := by
  have hHz := normalizer_eq_centralizer_of_card_two S.card2 (z_mem_V1 S) S.cfg.z_ne_one
  have hh : h ∈ Subgroup.centralizer ({S.cfg.z} : Set G) := hHz ▸ hhH
  exact Subgroup.mem_centralizer_singleton_iff.mp hh

theorem isFaithfulLocal_K₀ (h12213 : Stmt12_2_13) (h13322 : Stmt13_3_2_two)
    (hV : StmtL32NModule) {h t : G} {K₀ : Subgroup G} (hhH : h ∈ l32nH T V) (htT : t ∈ T)
    (htZ : t ∈ Subgroup.centralizer (T : Set G)) (ht1 : t ≠ 1)
    (hK₀ : K₀ ∈ cComp (Subgroup.centralizer ({t} : Set G)))
    (hLK : L.map (MulAut.conj h).toMonoidHom ≤ K₀) : quasithinIsFaithfulLocal T K₀ := by
  obtain ⟨P, hP⟩ := exists_sylow_of_quasithinIsSylowTwo S.hyp.fsu.sylow
  have hTX : T ≤ Subgroup.centralizer ({t} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp htZ x hx)
  have htp : IsPGroup 2 ↥(Subgroup.zpowers t) :=
    S.hyp.fsu.sylow.1.to_le (Subgroup.zpowers_le.mpr htT)
  have hO : pCoreOf 2 (Subgroup.centralizer ({t} : Set G)) ≠ ⊥ := fun hb =>
    ht1 (by have := mem_pCoreOf_centralizer htp; rwa [hb, Subgroup.mem_bot] at this)
  have hH : InH (P : Subgroup G) (Subgroup.centralizer ({t} : Set G)) := ⟨hP ▸ hTX, hO⟩
  have hchar := charTwo_of_inH S.hyp.fsu.qtke.2.1 P hH
  obtain ⟨-, -, hred⟩ := conjClosure_isTwoReducedIn_of_charTwo
    (isSylowTwoOf_of_sylow_le P hH.1) hchar (le_refl _)
  rw [← hP]
  refine isFaithfulLocal_of_commutator_ne_bot S.hyp.fsu.qtke.2.1 P hH hK₀ hred fun h0 => ?_
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at h0
  apply z_not_mem_centralizer S h12213 h13322 hV
  have hzΩ : S.cfg.z ∈ quasithinOmegaOneCenter (P : Subgroup G) := hP ▸ (z_mem_V1 S).2
  have hzK : S.cfg.z ∈ Subgroup.centralizer (K₀ : Set G) := h0 (le_conjClosure _ _ hzΩ)
  have hz' : h⁻¹ * S.cfg.z * h = S.cfg.z := by
    rw [mul_assoc, ← comm_z S hhH]
    group
  rw [Subgroup.mem_centralizer_iff]
  intro l hl
  have h1 := Subgroup.mem_centralizer_iff.mp hzK _ (hLK ⟨l, hl, rfl⟩)
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h1
  calc l * S.cfg.z = h⁻¹ * ((h * l * h⁻¹) * S.cfg.z) * h := by
        rw [show h⁻¹ * ((h * l * h⁻¹) * S.cfg.z) * h = l * (h⁻¹ * S.cfg.z * h) by group, hz']
    _ = h⁻¹ * (S.cfg.z * (h * l * h⁻¹)) * h := by rw [h1]
    _ = (h⁻¹ * S.cfg.z * h) * l := by group
    _ = S.cfg.z * l := by rw [hz']

theorem inf_pCoreOf_eq {h : G} {K₀ : Subgroup G} (hLK : L.map (MulAut.conj h).toMonoidHom ≤ K₀)
    (hK₀ : Nat.card (OTwoQuot K₀) ≤ 168) :
    L.map (MulAut.conj h).toMonoidHom ⊓ pCoreOf 2 K₀ = V.map (MulAut.conj h).toMonoidHom := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set L₀ := L.map (MulAut.conj h).toMonoidHom with hL₀
  have hO : pCoreOf 2 L₀ = V.map (MulAut.conj h).toMonoidHom := by
    rw [hL₀, pCoreOf_map_mulEquiv 2 (MulAut.conj h) L, ← S.vO]
  have hp : IsPGroup 2 ↥(L₀ ⊓ pCoreOf 2 K₀) := (pCoreOf_isPGroup 2 K₀).to_le inf_le_right
  have hn : L₀ ≤ Subgroup.normalizer ((L₀ ⊓ pCoreOf 2 K₀ : Subgroup G) : Set G) := fun x hx =>
    Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer hx, le_normalizer_pCoreOf 2 K₀ (hLK hx)⟩
  have hle : L₀ ⊓ pCoreOf 2 K₀ ≤ V.map (MulAut.conj h).toMonoidHom := by
    rw [← hO]
    exact le_pCoreOf_of_le_normalizer 2 inf_le_left hn hp
  have hL₀c : Nat.card L₀ = 1344 := by rw [hL₀, card_map_conj, S.cardL]
  have h1 := card_eq_card_imageOTwoQuot_mul K₀ L₀ hLK
  have h2 : Nat.card (imageOTwoQuot K₀ L₀) ≤ 168 := (Subgroup.card_le_card_group _).trans hK₀
  rw [hL₀c] at h1
  have h8 : Nat.card ↥(V.map (MulAut.conj h).toMonoidHom) = 8 := by rw [card_map_conj, S.card8]
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [h8]
  by_contra hlt
  push Not at hlt
  have h3 : Nat.card (imageOTwoQuot K₀ L₀) * Nat.card ↥(L₀ ⊓ pCoreOf 2 K₀) ≤ 168 * 7 :=
    Nat.mul_le_mul h2 (by omega)
  omega

end Setup

end L1444CTL

end CFSG.Quasithin.H13
