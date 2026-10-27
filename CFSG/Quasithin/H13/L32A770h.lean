module

public import CFSG.Quasithin.H13.L32A770g
public import CFSG.Quasithin.H13.L32A770f

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits
open CFSG.Quasithin.CosetGeom
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

theorem conjSub_u0_eq {a b : G} (hV1 : conjSub a (fsuV1 T V) = conjSub b (fsuV1 T V))
    (hU : conjSub a (fsuU T V) = conjSub b (fsuU T V))
    (hH : conjSub a (hz T V) = conjSub b (hz T V)) :
    conjSub a (u0 T V) = conjSub b (u0 T V) := by
  have hK : conjSub a (kz T V) = conjSub b (kz T V) := by
    have e : ∀ c : G, conjSub c (kz T V) = oTwoUpper (conjSub c (hz T V)) := fun c =>
      (oTwoUpper_map (MulAut.conj c).toMonoidHom (hz T V)).symm
    rw [e, e, hH]
  unfold u0
  rw [conjSub_centralizerMod, conjSub_centralizerMod, hV1, hU, hK]

namespace Not1471

variable {γ γ' : F8.Geom T L (hz T V)} {g k : ↥((L ⊔ T) ⊔ hz T V)}
  (N : Not1471 T L V (hz T V) γ γ' g k)
include N

theorem U_le_Gα (h : Hyp147 G T L V) (hMod : StmtL32NModule)
    (hF : HypF98 T V L (fsuV1 T V) V (hz T V))
    (h2 : (pCoreOf 2 (hz T V)).relIndex (conjSub (k : G) (F8.Uγ V (hz T V) (g : G)) ⊔
      pCoreOf 2 (hz T V)) = 2) :
    fsuU T V ≤ conjSub ((k : G) * g) (hz T V) := by
  obtain ⟨δ, δ', k₂, h₀, y, N', -, hW, hH, -, -, -⟩ := N.exists_sym70 h hMod hF h2
  have hle : conjSub ((h₀ : G) * k₂) (fsuU T V) ≤ hz T V := by
    rw [← uα_eq (g := k₂) (k := h₀) h hMod]
    exact (N'.uα_le hF).trans ((pCoreOf_le_of_le h le_sup_right).trans hF.T_le_H)
  have := conjSub_mono y hle
  rwa [hW, hH] at this

theorem F_le_Uα (h : Hyp147 G T L V) (hMod : StmtL32NModule)
    (hF : HypF98 T V L (fsuV1 T V) V (hz T V))
    (h2 : (pCoreOf 2 (hz T V)).relIndex (conjSub (k : G) (F8.Uγ V (hz T V) (g : G)) ⊔
      pCoreOf 2 (hz T V)) = 2) :
    ⁅fsuU T V, conjSub ((k : G) * g) (fsuU T V)⁆ ≤ conjSub ((k : G) * g) (fsuU T V) := by
  have hUN : fsuU T V ≤ Subgroup.normalizer (conjSub ((k : G) * g) (fsuU T V) : Set G) :=
    (N.U_le_Gα h hMod hF h2).trans (conjSub_le_normalizer (hz_le_normalizer_U h hMod) _)
  rw [Subgroup.commutator_le]
  intro u hu w hw
  have : u * w⁻¹ * u⁻¹ ∈ conjSub ((k : G) * g) (fsuU T V) :=
    (Subgroup.mem_normalizer_iff.mp (hUN hu) _).mp (inv_mem hw)
  rw [commutatorElement_def, show u * w * u⁻¹ * w⁻¹ = (u * w⁻¹ * u⁻¹)⁻¹ * w⁻¹ by group]
  exact mul_mem (inv_mem this) (inv_mem hw)

theorem commutator_v1_eq (h : Hyp147 G T L V) (hMod : StmtL32NModule) (h63 : Thm14_7_63)
    (hF : HypF98 T V L (fsuV1 T V) V (hz T V)) (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2)
    (h1334 : A6.Stmt13_3_4) (h13314 : A6.Stmt13_3_14) (h68 : Lemma14_7_68)
    (h69 : Lemma14_7_69)
    (h2 : (pCoreOf 2 (hz T V)).relIndex (conjSub (k : G) (F8.Uγ V (hz T V) (g : G)) ⊔
      pCoreOf 2 (hz T V)) = 2) :
    ⁅fsuV1 T V, conjSub ((k : G) * g) (pCoreOf 2 (hz T V))⁆ =
      conjSub ((k : G) * g) (fsuV1 T V) := by
  obtain ⟨δ, δ', k₂, h₀, y, N', -, -, hH, -, hV1, hV1'⟩ := N.exists_sym70 h hMod hF h2
  have h2' := h69 G T L V h δ δ' k₂ h₀ N'
  have he := N'.commutator_zα_eq h hMod h63 hF h1222 h1332 h1334 h13314 h68 h2'
  have e := congrArg (conjSub y) he
  rw [← conjSub_commutator, hV1', ← pCoreOf_conjSub, hH, pCoreOf_conjSub, hV1] at e
  exact e

theorem inf_u0α_eq (h : Hyp147 G T L V) (hMod : StmtL32NModule) (h63 : Thm14_7_63)
    (hF : HypF98 T V L (fsuV1 T V) V (hz T V)) (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2)
    (h1334 : A6.Stmt13_3_4) (h64 : Remark14_7_64) (h69 : Lemma14_7_69)
    (h2 : (pCoreOf 2 (hz T V)).relIndex (conjSub (k : G) (F8.Uγ V (hz T V) (g : G)) ⊔
      pCoreOf 2 (hz T V)) = 2) :
    ⁅fsuU T V, conjSub ((k : G) * g) (fsuU T V)⁆ ⊓ conjSub ((k : G) * g) (u0 T V) =
      conjSub ((k : G) * g) (fsuV1 T V) := by
  obtain ⟨δ, δ', k₂, h₀, y, N', hU, hW, hH, -, hV1, hV1'⟩ := N.exists_sym70 h hMod hF h2
  have h2' := h69 G T L V h δ δ' k₂ h₀ N'
  obtain ⟨s', hs'W, hs'Q, hW'⟩ := N'.exists_mem_not_mem h hMod hF h2'
  have he := N'.sup_inf_u0 h hMod hF h64 hs'W hs'Q hW'
  have e := congrArg (conjSub y) he
  rw [conjSub_inf, conjSub_sup, ← conjSub_commutator, hW, hU, hV1, conjSub_u0_eq hV1 hU hH,
    Subgroup.commutator_comm] at e
  have hZF := N.zα_le h hMod h63 hF h1222 h1332 h1334 h2
  rwa [sup_eq_left.mpr hZF] at e

theorem mem_zα_of_comm (h : Hyp147 G T L V) (hMod : StmtL32NModule) (h63 : Thm14_7_63)
    (hF : HypF98 T V L (fsuV1 T V) V (hz T V)) (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2)
    (h1334 : A6.Stmt13_3_4) (h13314 : A6.Stmt13_3_14) (h64 : Remark14_7_64)
    (h69 : Lemma14_7_69)
    (h2 : (pCoreOf 2 (hz T V)).relIndex (conjSub (k : G) (F8.Uγ V (hz T V) (g : G)) ⊔
      pCoreOf 2 (hz T V)) = 2) {f : G} (hf : f ∈ ⁅fsuU T V, conjSub ((k : G) * g) (fsuU T V)⁆)
    (hc : ∀ c ∈ conjSub ((k : G) * g) (pCoreOf 2 (hz T V)), c * f = f * c) :
    f ∈ conjSub ((k : G) * g) (fsuV1 T V) := by
  rw [← N.inf_u0α_eq h hMod h63 hF h1222 h1332 h1334 h64 h69 h2]
  refine ⟨hf, ?_⟩
  have hfW := N.F_le_Uα h hMod hF h2 hf
  show f ∈ conjSub ((k : G) * g) (u0 T V)
  rw [mem_conjSub] at hfW ⊢
  refine centralizer_le_u0 h hMod h63 hF h1222 h1332 h1334 h13314 hfW fun q hq => ?_
  have hcq := hc _ (mul_mem_conjSub (g := (k : G) * g) hq)
  have e : q = ((k : G) * g)⁻¹ * (((k : G) * g) * q * ((k : G) * g)⁻¹) * ((k : G) * g) := by
    group
  rw [e]
  calc ((k : G) * g)⁻¹ * (((k : G) * g) * q * ((k : G) * g)⁻¹) * ((k : G) * g) *
        (((k : G) * g)⁻¹ * f * ((k : G) * g)) =
        ((k : G) * g)⁻¹ * ((((k : G) * g) * q * ((k : G) * g)⁻¹) * f) * ((k : G) * g) := by
          group
    _ = ((k : G) * g)⁻¹ * (f * (((k : G) * g) * q * ((k : G) * g)⁻¹)) * ((k : G) * g) := by
          rw [hcq]
    _ = ((k : G) * g)⁻¹ * f * ((k : G) * g) *
        (((k : G) * g)⁻¹ * (((k : G) * g) * q * ((k : G) * g)⁻¹) * ((k : G) * g)) := by
          group

omit N in
theorem comm_mem_zα (h : Hyp147 G T L V) (hMod : StmtL32NModule)
    (hF : HypF98 T V L (fsuV1 T V) V (hz T V)) {c w : G}
    (hc : c ∈ conjSub ((k : G) * g) (pCoreOf 2 (hz T V)))
    (hw : w ∈ conjSub ((k : G) * g) (fsuU T V)) :
    c * w * c⁻¹ * w⁻¹ ∈ conjSub ((k : G) * g) (fsuV1 T V) := by
  rw [mem_conjSub] at hc hw ⊢
  have := comm_mem_of_pCoreOf h hMod hF hc hw
  rwa [show ((k : G) * g)⁻¹ * c * ((k : G) * g) * (((k : G) * g)⁻¹ * w * ((k : G) * g)) *
      (((k : G) * g)⁻¹ * c * ((k : G) * g))⁻¹ * (((k : G) * g)⁻¹ * w * ((k : G) * g))⁻¹ =
      ((k : G) * g)⁻¹ * (c * w * c⁻¹ * w⁻¹) * ((k : G) * g) by group] at this

theorem F_le_U (h : Hyp147 G T L V) (hMod : StmtL32NModule)
    (hF : HypF98 T V L (fsuV1 T V) V (hz T V)) :
    ⁅fsuU T V, conjSub ((k : G) * g) (fsuU T V)⁆ ≤ fsuU T V := by
  rw [Subgroup.commutator_le]
  intro u hu w hw
  have hwH : w ∈ hz T V := by
    have := N.uα_le hF
    rw [uα_eq (g := g) (k := k) h hMod] at this
    exact ((pCoreOf_le_of_le h le_sup_right).trans hF.T_le_H) (this hw)
  have hwu : w * u⁻¹ * w⁻¹ ∈ fsuU T V :=
    (Subgroup.mem_normalizer_iff.mp (hz_le_normalizer_U h hMod hwH) _).mp (inv_mem hu)
  rw [commutatorElement_def, show u * w * u⁻¹ * w⁻¹ = u * (w * u⁻¹ * w⁻¹) by group]
  exact mul_mem hu hwu

theorem exists_transvection (h : Hyp147 G T L V) (hMod : StmtL32NModule) (h63 : Thm14_7_63)
    (hF : HypF98 T V L (fsuV1 T V) V (hz T V)) (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2)
    (h1334 : A6.Stmt13_3_4) (h13314 : A6.Stmt13_3_14) (h64 : Remark14_7_64)
    (h69 : Lemma14_7_69)
    (h2 : (pCoreOf 2 (hz T V)).relIndex (conjSub (k : G) (F8.Uγ V (hz T V) (g : G)) ⊔
      pCoreOf 2 (hz T V)) = 2) {f : G} (hf : f ∈ ⁅fsuU T V, conjSub ((k : G) * g) (fsuU T V)⁆)
    (hfE : f ∉ fsuV1 T V ⊔ conjSub ((k : G) * g) (fsuV1 T V)) :
    ∃ c ∈ conjSub ((k : G) * g) (pCoreOf 2 (hz T V)), c ∈ hz T V ∧ c * f * c⁻¹ ≠ f := by
  obtain ⟨z, hz0, hz1, hgen⟩ := exists_gen_of_card_two hF.card_V₁
  have hZcard : Nat.card ↥(conjSub ((k : G) * g) (fsuV1 T V)) = 2 := by
    rw [conjSub, Subgroup.card_map_of_injective (MulAut.conj _).injective]
    exact hF.card_V₁
  obtain ⟨zα, hzα, hzα1, hgenα⟩ := exists_gen_of_card_two hZcard
  have hV1F := N.v1_le h hMod h63 hF h1222 h1332 h1334 h69 h2
  have hZF := N.zα_le h hMod h63 hF h1222 h1332 h1334 h2
  have hFW := N.F_le_Uα h hMod hF h2
  have hFU := N.F_le_U h hMod hF
  have hzF := hV1F hz0
  have hzαF := hZF hzα
  have hzα2 : zα * zα = 1 := by
    have h3 : (⟨zα, hzα⟩ : ↥(conjSub ((k : G) * g) (fsuV1 T V))) ^ 2 = 1 := by
      rw [← hZcard]
      exact pow_card_eq_one'
    rw [sq] at h3
    simpa using congrArg Subtype.val h3
  have hcomm : ∀ a ∈ ⁅fsuU T V, conjSub ((k : G) * g) (fsuU T V)⁆,
      ∀ b ∈ ⁅fsuU T V, conjSub ((k : G) * g) (fsuU T V)⁆, a * b = b * a :=
    fun a ha b hb => fsuU_comm h (hFU ha) (hFU hb)
  have hact : ∀ c ∈ conjSub ((k : G) * g) (pCoreOf 2 (hz T V)),
      ∀ x ∈ ⁅fsuU T V, conjSub ((k : G) * g) (fsuU T V)⁆,
      c * x * c⁻¹ = x ∨ c * x * c⁻¹ = zα * x := by
    intro c hc x hx
    rcases hgenα _ (comm_mem_zα h hMod hF hc (hFW hx)) with e | e
    · left
      calc c * x * c⁻¹ = c * x * c⁻¹ * x⁻¹ * x := by group
        _ = x := by rw [e, one_mul]
    · right
      calc c * x * c⁻¹ = c * x * c⁻¹ * x⁻¹ * x := by group
        _ = zα * x := by rw [e]
  have hfixα : ∀ c ∈ conjSub ((k : G) * g) (pCoreOf 2 (hz T V)), c * zα * c⁻¹ = zα := by
    intro c hc
    have hc' : c ∈ conjSub ((k : G) * g) (hz T V) := conjSub_mono _ (pCoreOf_le 2 _) hc
    rw [mem_conjSub] at hc'
    have hzα' : ((k : G) * g)⁻¹ * zα * ((k : G) * g) ∈ fsuV1 T V := by
      rw [← mem_conjSub]; exact hzα
    have e := Subgroup.mem_centralizer_iff.mp hc' _ hzα'
    calc c * zα * c⁻¹ = ((k : G) * g) * ((((k : G) * g)⁻¹ * c * ((k : G) * g)) *
          (((k : G) * g)⁻¹ * zα * ((k : G) * g))) * (((k : G) * g)⁻¹ * c⁻¹ * ((k : G) * g)) *
          ((k : G) * g)⁻¹ := by group
      _ = ((k : G) * g) * ((((k : G) * g)⁻¹ * zα * ((k : G) * g)) *
          (((k : G) * g)⁻¹ * c * ((k : G) * g))) * (((k : G) * g)⁻¹ * c⁻¹ * ((k : G) * g)) *
          ((k : G) * g)⁻¹ := by rw [← e]
      _ = zα := by group
  have hmemH : ∀ c : G, c * z * c⁻¹ = z → c ∈ hz T V := by
    intro c hcz
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    rcases hgen v hv with rfl | rfl
    · group
    · calc v * c = c * v * c⁻¹ * c := by rw [hcz]
        _ = c * v := by group
  have hmove : ∀ x ∈ ⁅fsuU T V, conjSub ((k : G) * g) (fsuU T V)⁆,
      x ∉ conjSub ((k : G) * g) (fsuV1 T V) →
      ∃ c ∈ conjSub ((k : G) * g) (pCoreOf 2 (hz T V)), c * x * c⁻¹ ≠ x := by
    intro x hx hxZ
    by_contra hc
    push Not at hc
    refine hxZ (N.mem_zα_of_comm h hMod h63 hF h1222 h1332 h1334 h13314 h64 h69 h2 hx
      fun c hc' => ?_)
    calc c * x = c * x * c⁻¹ * c := by group
      _ = x * c := by rw [hc c hc']
  have hfZ : f ∉ conjSub ((k : G) * g) (fsuV1 T V) := fun h' => hfE (Subgroup.mem_sup_right h')
  have hzfZ : z * f ∉ conjSub ((k : G) * g) (fsuV1 T V) := fun h' => hfE (by
    rw [show f = z⁻¹ * (z * f) by group]
    exact mul_mem (Subgroup.mem_sup_left (inv_mem hz0)) (Subgroup.mem_sup_right h'))
  obtain ⟨c₂, hc₂, hc₂f⟩ := hmove f hf hfZ
  rcases hact c₂ hc₂ z hzF with hc₂z | hc₂z
  · exact ⟨c₂, hc₂, hmemH c₂ hc₂z, hc₂f⟩
  obtain ⟨c₃, hc₃, hc₃zf⟩ := hmove (z * f) (mul_mem hzF hf) hzfZ
  have hmul : ∀ c : G, c * (z * f) * c⁻¹ = (c * z * c⁻¹) * (c * f * c⁻¹) := fun c => by group
  rcases hact c₃ hc₃ z hzF with hc₃z | hc₃z
  · refine ⟨c₃, hc₃, hmemH c₃ hc₃z, fun e => hc₃zf ?_⟩
    rw [hmul, hc₃z, e]
  have hc₃f : c₃ * f * c₃⁻¹ = f := by
    rcases hact c₃ hc₃ f hf with e | e
    · exact e
    · exfalso
      apply hc₃zf
      rw [hmul, hc₃z, e]
      calc zα * z * (zα * f) = z * (zα * zα) * f := by rw [hcomm zα hzαF z hzF]; group
        _ = z * f := by rw [hzα2, mul_one]
  have hc₂f' : c₂ * f * c₂⁻¹ = zα * f := (hact c₂ hc₂ f hf).resolve_left hc₂f
  refine ⟨c₂ * c₃, mul_mem hc₂ hc₃, hmemH _ ?_, ?_⟩
  · calc c₂ * c₃ * z * (c₂ * c₃)⁻¹ = c₂ * (c₃ * z * c₃⁻¹) * c₂⁻¹ := by group
      _ = (c₂ * zα * c₂⁻¹) * (c₂ * z * c₂⁻¹) := by rw [hc₃z]; group
      _ = zα * (zα * z) := by rw [hfixα c₂ hc₂, hc₂z]
      _ = z := by rw [← mul_assoc, hzα2, one_mul]
  · calc c₂ * c₃ * f * (c₂ * c₃)⁻¹ = c₂ * (c₃ * f * c₃⁻¹) * c₂⁻¹ := by group
      _ = zα * f := by rw [hc₃f, hc₂f']
      _ ≠ f := fun e => hzα1 (by
          calc zα = zα * f * f⁻¹ := by group
            _ = 1 := by rw [e, mul_inv_cancel])

end Not1471

end CFSG.Quasithin.H13.L32A
