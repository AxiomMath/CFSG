module

public import CFSG.Quasithin.Background.A1aFStar
public import CFSG.Quasithin.Vol2.Ch12Sec8OneLemma8
public import CFSG.Quasithin.H13.L32NInputs
public import CFSG.Quasithin.H13.L32NModule

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint
open scoped IsMulCommutative

variable {G : Type} [Group G]

section CenterU

variable {T V : Subgroup G}

theorem fsuV1_le_centerOf_of_decomp {U₀ : Subgroup G}
    (hU₀Z : U₀ ⊔ centerOf (fsuU T V) = fsuU T V)
    (hext : CFSG.IsExtraspecialPGroup 2 ↥U₀) (hΦ : frattiniOf U₀ = fsuV1 T V) :
    fsuV1 T V ≤ centerOf (fsuU T V) := by
  have hV1U : fsuV1 T V ≤ fsuU T V := inf_le_left.trans (le_conjClosure V _)
  refine le_inf hV1U ?_
  rw [← Subgroup.le_centralizer_iff, ← hU₀Z]
  refine sup_le ?_ ((inf_le_right.trans (Subgroup.centralizer_le hV1U)))
  intro u hu
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  rw [← hΦ] at hv
  obtain ⟨c, hc, rfl⟩ := hv
  rw [hext.2.2.1] at hc
  have := Subgroup.mem_center_iff.mp hc ⟨u, hu⟩
  exact (congrArg Subtype.val this).symm

end CenterU

namespace Hyp14310One

variable [Finite G] {T L V : Subgroup G}

theorem isPGroup_fsuV1 (h : Hyp14310One G T L V) : IsPGroup 2 (fsuV1 T V) :=
  h.fsu.sylow.1.to_le (inf_le_right.trans
    ((Subgroup.closure_le _).mpr fun _ hz => hz.1.1))

theorem charTwo_l32nH (h : Hyp14310One G T L V) (hV : StmtL32NModule) :
    l32nH T V ⊓ Subgroup.centralizer (pCoreOf 2 (l32nH T V) : Set G) ≤
      pCoreOf 2 (l32nH T V) := by
  obtain ⟨S, hS⟩ := exists_sylow_of_quasithinIsSylowTwo h.fsu.sylow
  have hne : fsuV1 T V ≠ ⊥ := by
    intro hb
    have h2 := (hV G T L V h.hyp h.fsu).2.2.2.1
    rw [hb, Subgroup.card_bot] at h2
    omega
  exact h.fsu.qtke.2.1 (l32nH T V) ⟨fsuV1 T V, hne, h.isPGroup_fsuV1, rfl⟩
    ⟨S, hS ▸ h.le_l32nH hV⟩

theorem quasithinGenFitting_l32nH (h : Hyp14310One G T L V) (hV : StmtL32NModule) :
    quasithinGenFitting (l32nH T V) = pCoreOf 2 (l32nH T V) :=
  (quasithinGenFitting_eq_pCoreOf_iff _ 2).mpr (h.charTwo_l32nH hV)

theorem isTypeHS (h : Hyp14310One G T L V) (hV : StmtL32NModule) (h1433 : Lemma1433Five)
    (c32 : Concl14332 T V) (c33 : Concl14333 T L V) : HSType.IsTypeHS G := by
  obtain ⟨hVe, hV8, hLTV, hV1, -⟩ := hV G T L V h.hyp h.fsu
  obtain ⟨z, hz1⟩ : ∃ z : ↥(fsuV1 T V), z ≠ 1 := by
    by_contra hall
    push Not at hall
    have : Nat.card ↥(fsuV1 T V) = 1 := Nat.card_eq_one_iff_unique.mpr
      ⟨⟨fun a b => (hall a).trans (hall b).symm⟩, inferInstance⟩
    omega
  have hz : (z : G) ≠ 1 := fun h0 => hz1 (Subtype.ext h0)
  have hzV : (z : G) ∈ V := z.2.1
  have hord : orderOf (z : G) = 2 :=
    orderOf_eq_prime (by simpa using hVe.2 (z : G) hzV) hz
  have hHz : l32nH T V = Subgroup.centralizer ({(z : G)} : Set G) :=
    normalizer_eq_centralizer_of_card_two hV1 z.2 hz
  have hF : quasithinGenFitting (Subgroup.centralizer ({(z : G)} : Set G)) = fsuU T V := by
    rw [← hHz, h.quasithinGenFitting_l32nH hV, ← c33.u_eq_q]
  have hNV : Subgroup.normalizer (V : Set G) = L := by
    rw [h1433 G T L V h.hyp h.fsu, c33.m_eq]
    exact inf_eq_left.mpr (le_sup_left.trans hLTV)
  have hFL : quasithinGenFitting L = pCoreOf 2 L := h.fsu.faithful.2.2.1
  refine ⟨z, V, hord, hVe, hV8, ⟨?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩
  · rw [hF]
    exact c32.z4q8q8
  · rw [← hHz, h.quasithinGenFitting_l32nH hV, c32.q_eq]
    exact c32.sym
  · rw [hF]
    exact le_conjClosure V _
  · rw [hNV, hFL]
    exact c33.p_iso
  · rw [hNV, hFL]
    exact exists_surj_SL32_of_lieModel h.hyp.linear

end Hyp14310One

theorem thm14326One_of_inputs (hI48 : HSType.StatementI48) (h1332 : Stmt13_3_2)
    (h1334 : A6.Stmt13_3_4) (h1222 : Stmt12_2_2) (h12213 : Stmt12_2_13) (h1433 : Lemma1433Five)
    (h14332 : Lemma14332) (h14333 : Lemma14333) : Thm14326One := by
  intro G _ _ T L V h
  have h13322 := stmt13_3_2_two_of_stmt13_3_2 h1332
  have hV := stmtL32NModule_of_inputs h1332 h1334
  obtain ⟨V₂, hV₂⟩ := h.exists_plane hV
  obtain ⟨⟨U₀, -, hext, hΦ, hU₀Z⟩, -⟩ :=
    lemma12_8_8_n3 h1222 h12213 (h.setting1282One h13322 hV hV₂)
  have hV1Z := fsuV1_le_centerOf_of_decomp hU₀Z hext hΦ
  by_cases hlt : fsuV1 T V < centerOf (fsuU T V)
  · exact Or.inr (hI48 G (h.isTypeHS hV h1433 (h14332 G T L V h hlt) (h14333 G T L V h hlt)))
  · have heq : centerOf (fsuU T V) = fsuV1 T V := (eq_of_le_of_not_lt hV1Z hlt).symm
    have hUU : fsuU T V = U₀ := by
      have h1 : U₀ ⊔ centerOf (fsuU T V) = fsuU T V := hU₀Z
      rw [← h1, heq, ← hΦ]
      exact sup_eq_left.mpr (Subgroup.map_subtype_le _)
    refine Or.inl ⟨heq, ?_⟩
    rw [hUU]
    exact hext

end CFSG.Quasithin.H13
