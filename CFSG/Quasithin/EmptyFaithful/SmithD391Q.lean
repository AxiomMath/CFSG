module

public import CFSG.Quasithin.EmptyFaithful.SmithD391TwistQ
public import CFSG.Quasithin.Background.F918N3
public import CFSG.Quasithin.Background.F918M0
public import CFSG.Quasithin.Background.F918N6
public import CFSG.Quasithin.EmptyFaithful.S153ZP
public import CFSG.Quasithin.EmptyFaithful.SmithD391Setup

public section

namespace CFSG.Quasithin.SmithD391

open CFSG.Quasithin.Z391 CFSG.Quasithin.F918X CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.QuasithinUnique
open scoped Pointwise

variable {W : Type} [CommGroup W] [Finite W] {M T L : Subgroup (MulAut W)} {V : Subgroup W}

@[expose, reducible] noncomputable def qAct (hML : M ≤ Subgroup.normalizer (L : Set (MulAut W))) :
    MulDistribMulAction ↥M (W ⧸ modFix L (⊤ : Subgroup W)) :=
  quotAct (W := (⊤ : Subgroup W)) hML (fun _ _ _ _ => trivial)

theorem d391_T_le (hD : D3Std M L T L V) : T ≤ Subgroup.normalizer (L : Set (MulAut W)) := by
  calc T ≤ Subgroup.normalizer (conjClosure L T : Set (MulAut W)) := le_normalizer_conjClosure L T
    _ = Subgroup.normalizer (L : Set (MulAut W)) := by rw [← hD.hyp.Mp_eq]

theorem d391_Λ_normal (hD : D3Std M L T L V) :
    ∀ g : ↥M, ∀ l ∈ L.subgroupOf M, g * l * g⁻¹ ∈ L.subgroupOf M := fun g l hl =>
  ((Subgroup.mem_normalizer_iff.1 (hD.hyp.Mp_normal g.2)) (l : MulAut W)).1 hl

theorem isIrr_tildeQ (hD : D3Std M L T L V) :
    letI := qAct hD.hyp.Mp_normal
    XMod.IsIrr ↥(L.subgroupOf M) (tilde L ⊤ V) := by
  let _i := qAct hD.hyp.Mp_normal
  have hirr := (isIrr_tilde hD.hyp.irr).1
  have hLM : L ≤ M := le_of_mem_cComp hD.hyp.comp
  let φ : ↥(L.subgroupOf M) → ↥L := fun l => ⟨((l : ↥M) : MulAut W), l.2⟩
  have hφ : Function.Surjective φ := fun a => ⟨⟨⟨(a : MulAut W), hLM a.2⟩, a.2⟩, rfl⟩
  have hact : ∀ (l : ↥(L.subgroupOf M)) (x : W ⧸ modFix L (⊤ : Subgroup W)), l • x = φ l • x := by
    intro l x
    induction x using QuotientGroup.induction_on with
    | H v => rfl
  exact isIrr_of_surj φ hφ hact hirr

omit [Finite W] in
theorem smul_tildeQ (hML : M ≤ Subgroup.normalizer (L : Set (MulAut W))) (g : ↥M)
    (I : Subgroup W) :
    letI := qAct hML
    g • tilde L ⊤ I = tilde L ⊤ ((g : MulAut W) • I) :=
  tilde_smul (W := (⊤ : Subgroup W)) hML (fun _ _ _ _ => trivial) g I

theorem iSup_smul_tildeQ (hD : D3Std M L T L V) :
    letI := qAct hD.hyp.Mp_normal
    (⨆ g : ↥M, g • tilde L ⊤ V) = ⊤ := by
  let _i := qAct hD.hyp.Mp_normal
  have e : ∀ g : ↥M, g • tilde L ⊤ V = tilde L ⊤ ((g : MulAut W) • V) :=
    fun g => smul_tildeQ hD.hyp.Mp_normal g V
  rw [iSup_congr e, ← tilde_biSup M V]
  have : (⨆ y ∈ M, y • V) = ⊤ := hD.hyp.gen
  rw [this]
  exact Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)

theorem not_iso_tildeQ (hD : D3Std M L T L V) (hlt : V < orbSup T V)
    (hC : ∀ g ∈ L, (∀ v ∈ V, g v = v) → ∀ x ∈ L, g * x = x * g) {t : MulAut W} (htT : t ∈ T)
    (htM : t ∈ M) (htn : t ∉ stabSub V) :
    letI := qAct hD.hyp.Mp_normal
    ¬ XMod.Iso ↥(L.subgroupOf M) ((⟨t, htM⟩ : ↥M) • tilde L ⊤ V) (tilde L ⊤ V) := by
  let _i := qAct hD.hyp.Mp_normal
  intro hiso
  set VT := orbSup T V with hVT
  set C := VT ⊓ fixV L with hC'
  have hZ := z35_of_d3Std hD hlt hC
  have hG := n1_sup_le_stabSub_sec hD.hyp
  have hLM : L ≤ M := le_of_mem_cComp hD.hyp.comp
  have hpre : ∀ m : ↥(autSec L VT C), ∃ g : ↥(stabSub VT ⊓ stabSub C),
      (g : MulAut W) ∈ L ∧ n2Rho VT C g = m :=
    fun m => (n2_mem_autSec ((le_sup_left : L ≤ L ⊔ T).trans hG)).1 m.2
  choose g hgL hgm using hpre
  let f : ↥(autSec L VT C) → ↥(L.subgroupOf M) := fun m => ⟨⟨g m, hLM (hgL m)⟩, hgL m⟩
  have hf : ∀ (m : ↥(autSec L VT C)) (x : Sec VT C),
      iotaQ L VT (m • x) = f m • iotaQ L VT x := by
    intro m x
    show iotaQ L VT ((m : MulAut (Sec VT C)) x) = _
    rw [← hgm m]
    exact iotaQ_rho hD.hyp.Mp_normal (g m) (hLM (hgL m)) x
  have hV₀ : V ≤ VT := le_orbSup T V
  have htV : t • V ≤ VT := map_le_orbSup htT
  have h1 : (⟨t, htM⟩ : ↥M) • tilde L ⊤ V = (sec35Img VT C (t • V)).map (iotaQ L VT) := by
    rw [smul_tildeQ hD.hyp.Mp_normal, map_iotaQ_sec35Img L htV]
  have h2 : tilde L ⊤ V = (sec35Img VT C V).map (iotaQ L VT) := (map_iotaQ_sec35Img L hV₀).symm
  rw [h1, h2] at hiso
  have hisoX := iso_of_iso_map (iotaQ L VT) (iotaQ_injective L VT) f hf hiso
  set tg : ↥(stabSub VT ⊓ stabSub C) := ⟨t, hG ((le_sup_right : T ≤ L ⊔ T) htT)⟩ with htg
  have htX : n2Rho VT C tg ∈ autSec T VT C :=
    (n2_mem_autSec ((le_sup_right : T ≤ L ⊔ T).trans hG)).2 ⟨tg, htT, rfl⟩
  have hmap : sec35Img VT C (t • V) = (sec35Img VT C V).map (n2Rho VT C tg).toMonoidHom :=
    (n2_map_rho_sec35Img tg V).symm
  rw [hmap] at hisoX
  have h3 := hZ.homog _ htX 1 (one_mem _) (by rw [n6_map_one]; exact hisoX)
  rw [n6_map_one] at h3
  have h4 : tilde L ⊤ (t • V) = tilde L ⊤ V := by
    rw [← map_iotaQ_sec35Img L htV, ← map_iotaQ_sec35Img L hV₀, hmap, h3]
  obtain ⟨-, hVcomm, -, -⟩ := mem_irrPlus_top_iff.1 hD.hyp.irr
  have hcomm : modComm L V = V := by
    show XMod.commOf ↥L V = V
    rw [commOf_eq_commSub]
    exact hVcomm
  have h5 := smul_eq_of_tilde_eq (W := (⊤ : Subgroup W)) (d391_T_le hD) hcomm htT h4
  exact htn (mem_stabSub_iff_map_eq.2 h5)

theorem injective_twoClass_tildeQ (hD : D3Std M L T L V) (h5 : D35Five L V) :
    letI := qAct hD.hyp.Mp_normal
    Function.Injective (actAut (L.subgroupOf M) (tilde L ⊤ V) (isIrr_tildeQ hD).1) ∧
      TwoClassMod (actAut (L.subgroupOf M) (tilde L ⊤ V) (isIrr_tildeQ hD).1).range := by
  let _i := qAct hD.hyp.Mp_normal
  have hLM : L ≤ M := le_of_mem_cComp hD.hyp.comp
  let ψ : ↥L →* ↥(L.subgroupOf M) := (Subgroup.subgroupOfEquivOfLe hLM).symm.toMonoidHom
  have hψ : Function.Surjective ψ := (Subgroup.subgroupOfEquivOfLe hLM).symm.surjective
  let f : ↥V →* ↥(tilde L ⊤ V) := (QuotientGroup.mk' (modFix L (⊤ : Subgroup W))).subgroupMap V
  have hf : Function.Surjective f :=
    (QuotientGroup.mk' (modFix L (⊤ : Subgroup W))).subgroupMap_surjective V
  have hfker : ∀ u : ↥V, f u = 1 ↔ (u : W) ∈ V ⊓ fixV L := by
    intro u
    constructor
    · intro h1
      have h2 : (QuotientGroup.mk (u : W) : W ⧸ modFix L (⊤ : Subgroup W)) = 1 :=
        congrArg Subtype.val h1
      rw [QuotientGroup.eq_one_iff, modFix_top_eq] at h2
      exact ⟨u.2, h2⟩
    · intro h1
      apply Subtype.ext
      show (QuotientGroup.mk (u : W) : W ⧸ modFix L (⊤ : Subgroup W)) = 1
      rw [QuotientGroup.eq_one_iff, modFix_top_eq]
      exact h1.2
  exact twoClass_injective_of_d35Five _ h5 ψ hψ f hf hfker (fun h u hu => rfl)

theorem iso_or_iso_tildeQ (hD : D3Std M L T L V) (hlt : V < orbSup T V)
    (hC : ∀ g ∈ L, (∀ v ∈ V, g v = v) → ∀ x ∈ L, g * x = x * g) (h5 : D35Five L V)
    {t : MulAut W} (htT : t ∈ T) (htM : t ∈ M) (htn : t ∉ stabSub V) :
    letI := qAct hD.hyp.Mp_normal
    ∀ g : ↥M, XMod.Iso ↥(L.subgroupOf M) (g • tilde L ⊤ V) (tilde L ⊤ V) ∨
      XMod.Iso ↥(L.subgroupOf M) (g • tilde L ⊤ V) ((⟨t, htM⟩ : ↥M) • tilde L ⊤ V) := by
  let _i := qAct hD.hyp.Mp_normal
  intro g
  have hirr := isIrr_tildeQ hD
  obtain ⟨hinj, htc⟩ := injective_twoClass_tildeQ hD h5
  have hN := normalizes_whole (Q := W ⧸ modFix L (⊤ : Subgroup W)) (L.subgroupOf M)
    (d391_Λ_normal hD)
  have hnot := not_iso_tildeQ hD hlt hC htT htM htn
  have hnot' : ¬ XMod.Iso ↥(L.subgroupOf M) (tilde L ⊤ V) ((⟨t, htM⟩ : ↥M) • tilde L ⊤ V) :=
    fun h => hnot (XMod.Iso.symm hirr.1 h)
  have hinvg := XMod.isInv_smul_of_normalizes hN g hirr.1
  have hinvt := XMod.isInv_smul_of_normalizes hN ⟨t, htM⟩ hirr.1
  rcases iso_or_iso_of_twoClass (d391_Λ_normal hD) hirr.1 hinj htc hnot' g with h | h
  · exact Or.inl (XMod.Iso.symm hirr.1 h)
  · exact Or.inr (XMod.Iso.symm hinvt h)

end CFSG.Quasithin.SmithD391
