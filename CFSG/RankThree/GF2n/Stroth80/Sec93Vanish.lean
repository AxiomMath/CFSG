module

public import CFSG.RankThree.GF2n.Stroth80.Sec93VanishStmt
public import CFSG.RankThree.GF2n.Stroth80.Sec311Conj
public import CFSG.RankThree.GF2n.Stroth80.HeringSec9Head
public import CFSG.RankThree.GF2n.Stroth80.HeringSec95CN6
public import CFSG.RankThree.GF2n.Stroth80.HeringSec95CStmt

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

namespace HS93

theorem eq_or_eq_of_simple {R X Y D Q : Subgroup G}
    (hXR : X ≤ R) (hYR : Y ≤ R) (hXY : X ⊔ Y = R) (hQ : X ⊓ Y = Q)
    (hXYn : X ≤ Subgroup.normalizer (Y : Set G))
    (hDR : D ≤ R) (hDnorm : R ≤ Subgroup.normalizer (D : Set G)) (hXD : X ≤ D)
    (hsimple : ∃ _ : (Q.subgroupOf Y).Normal, IsSimpleGroup (↥Y ⧸ Q.subgroupOf Y)) :
    D = X ∨ D = R := by
  obtain ⟨hNQ, hsim⟩ := hsimple
  have hYD : Y ≤ Subgroup.normalizer (D : Set G) := hYR.trans hDnorm
  have hQX : Q ≤ X := by rw [← hQ]; exact inf_le_left
  have hQY : Q ≤ Y := by rw [← hQ]; exact inf_le_right
  have hQD : Q ≤ D := hQX.trans hXD
  have hdec : ∀ {r : G}, r ∈ R → ∃ x ∈ X, ∃ y ∈ Y, x * y = r := by
    intro r hr
    have hr' : r ∈ (↑(X ⊔ Y) : Set G) := by rw [hXY]; exact hr
    rw [Subgroup.coe_mul_of_left_le_normalizer_right X Y hXYn] at hr'
    obtain ⟨x, hx, y, hy, hxy⟩ := Set.mem_mul.mp hr'
    exact ⟨x, hx, y, hy, hxy⟩
  have hN : ((D.subgroupOf Y).map (QuotientGroup.mk' (Q.subgroupOf Y))).Normal :=
    Subgroup.Normal.map (Subgroup.normal_subgroupOf_of_le_normalizer hYD) _
      (QuotientGroup.mk'_surjective _)
  rcases Subgroup.Normal.eq_bot_or_eq_top
      ((D.subgroupOf Y).map (QuotientGroup.mk' (Q.subgroupOf Y))) with h0 | h0
  · left
    have hDQ : ∀ y : Y, (y : G) ∈ D → (y : G) ∈ Q := by
      intro y hy
      have hmem : QuotientGroup.mk' (Q.subgroupOf Y) y ∈
          (D.subgroupOf Y).map (QuotientGroup.mk' (Q.subgroupOf Y)) :=
        Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hy)
      rw [h0, Subgroup.mem_bot, QuotientGroup.mk'_apply] at hmem
      exact Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff y).mp hmem)
    refine le_antisymm ?_ hXD
    intro d hd
    obtain ⟨x, hx, y, hy, hxy⟩ := hdec (hDR hd)
    have hyD : y ∈ D := by
      have h1 : x⁻¹ * d ∈ D := D.mul_mem (D.inv_mem (hXD hx)) hd
      rwa [← hxy, inv_mul_cancel_left] at h1
    have hyQ : y ∈ Q := hDQ ⟨y, hy⟩ hyD
    rw [← hxy]
    exact X.mul_mem hx (hQX hyQ)
  · right
    have hYD' : Y ≤ D := by
      intro y hy
      have hmem : QuotientGroup.mk' (Q.subgroupOf Y) (⟨y, hy⟩ : Y) ∈
          (D.subgroupOf Y).map (QuotientGroup.mk' (Q.subgroupOf Y)) := by
        rw [h0]
        exact Subgroup.mem_top _
      obtain ⟨d, hd, hdy⟩ := Subgroup.mem_map.mp hmem
      have hdD : (d : G) ∈ D := Subgroup.mem_subgroupOf.mp hd
      simp only [QuotientGroup.mk'_apply] at hdy
      have hq : (d⁻¹ * ⟨y, hy⟩ : Y) ∈ Q.subgroupOf Y := QuotientGroup.eq.mp hdy
      have hq' : ((d⁻¹ * ⟨y, hy⟩ : Y) : G) ∈ Q := Subgroup.mem_subgroupOf.mp hq
      have hyeq : y = (d : G) * ((d⁻¹ * ⟨y, hy⟩ : Y) : G) := by
        simp
      rw [hyeq]
      exact D.mul_mem hdD (hQD hq')
    refine le_antisymm hDR ?_
    intro r hr
    obtain ⟨x, hx, y, hy, hxy⟩ := hdec hr
    rw [← hxy]
    exact D.mul_mem (hXD hx) (hYD' hy)


theorem norm_Q (hc : Ctx M Q Z B) {g : G} (hgM : g ∈ M) {a : G} (ha : a ∈ Q) :
    g * a * g⁻¹ ∈ Q :=
  (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hgM) a).mp ha

theorem conj_mem' {S : Subgroup G} {x : G} (g : G) (hx : x ∈ S) :
    g * x * g⁻¹ ∈ conjSubgroup g S := by
  rw [mem_conjSubgroup]
  have e : g⁻¹ * (g * x * g⁻¹) * g = x := by group
  rw [e]
  exact hx

theorem mem_normalizer_of {H : Subgroup G} {g : G} (hg : ∀ h ∈ H, g * h * g⁻¹ ∈ H)
    (hg' : ∀ h ∈ H, g⁻¹ * h * g ∈ H) : g ∈ Subgroup.normalizer (H : Set G) :=
  Subgroup.mem_normalizer_iff.mpr fun h => ⟨fun hh => hg h hh, fun hh => by
    simpa [mul_assoc] using hg' _ hh⟩

theorem conj_mem_CN (hc : Ctx M Q Z B) {t : G} (ht : t ∈ LB M Q B) {ρ a : G}
    (hρ : ρ ∈ Rt M (LB M Q B) t) (ha : a ∈ hc.CN t) : ρ * a * ρ⁻¹ ∈ hc.CN t := by
  rw [Ctx.mem_CN] at ha ⊢
  refine ⟨(Rt M (LB M Q B) t).mul_mem ((Rt M (LB M Q B) t).mul_mem hρ ha.1)
    ((Rt M (LB M Q B) t).inv_mem hρ), fun v hv => ?_⟩
  have hv' : ρ⁻¹ * v * ρ ∈ Vt M (LB M Q B) B Z t := by
    have := (Subgroup.mem_normalizer_iff.mp
      (hc.Rt_normalizes_Vt ht ((Rt M (LB M Q B) t).inv_mem hρ)) v).mp hv
    simpa using this
  have h1 := ha.2 _ hv'
  have e : ⁅ρ * a * ρ⁻¹, v⁆ = ρ * ⁅a, ρ⁻¹ * v * ρ⁆ * ρ⁻¹ := by
    simp only [commutatorElement_def]; group
  rw [e]
  have hρM : ρ ∈ M := hc.Rt_le_M t hρ
  have := (Subgroup.mem_normalizer_iff.mp (hc.hyp.Z_normal.2 hρM) _).mp h1
  simpa using this

def CWV (hc : Ctx M Q Z B) (t : G) (ht : t ∈ LB M Q B) : Subgroup G where
  carrier := {a | a ∈ Rt M (LB M Q B) t ∧
    ∀ w ∈ Wt Q (Vt M (LB M Q B) B Z t), ⁅a, w⁆ ∈ Vt M (LB M Q B) B Z t}
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨(Rt M (LB M Q B) t).mul_mem ha hb, fun w hw => ?_⟩
    have e : ⁅a * b, w⁆ = a * ⁅b, w⁆ * a⁻¹ * ⁅a, w⁆ := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact (Vt M (LB M Q B) B Z t).mul_mem
      ((Subgroup.mem_normalizer_iff.mp (hc.Rt_normalizes_Vt ht ha) _).mp (hb' w hw))
        (ha' w hw) |> fun h => by simpa using h
  one_mem' := ⟨(Rt M (LB M Q B) t).one_mem, fun w _ => by simp [commutatorElement_def]⟩
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨(Rt M (LB M Q B) t).inv_mem ha, fun w hw => ?_⟩
    have e : ⁅a⁻¹, w⁆ = a⁻¹ * ⁅a, w⁆⁻¹ * a := by
      simp only [commutatorElement_def]; group
    rw [e]
    have h1 := (Vt M (LB M Q B) B Z t).inv_mem (ha' w hw)
    have := (Subgroup.mem_normalizer_iff.mp
      (hc.Rt_normalizes_Vt ht ((Rt M (LB M Q B) t).inv_mem ha)) _).mp h1
    simpa using this


theorem conj_Vt_of_centre (hCentre : Step95CentreStatement) {hc : Ctx M Q Z B} {n : ℕ} {t : G}
    (hs : Sec9Hyp hc n t) {Z0 : Subgroup G} (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q)
    {s z : G} (hT : Sec9T1 M Q Z0 s z) :
    conjSubgroup (z * s * z⁻¹) (Vt M (LB M Q B) B Z t) = Vt M (LB M Q B) B Z t := by
  classical
  obtain ⟨-, -, hV⟩ := hCentre G M Q Z B hc n t hs Z0 hZ0
  have ht : t ∈ LB M Q B := hs.mem
  have hQZ0 : Q ≤ Z0 := fun a ha => (hZ0 a).mpr ⟨hc.Q_le_Rt ht ha, fun r hr => by
    have hrM : r ∈ M := hc.Rt_le_M t hr
    have h1 := norm_Q hc hrM (Q.inv_mem ha)
    have e : ⁅a, r⁆ = a * (r * a⁻¹ * r⁻¹) := by simp only [commutatorElement_def]; group
    rw [e]
    exact Q.mul_mem ha h1⟩
  have hsQ : s ∉ Q := fun hsQ => hT.not_mem (hQZ0 (norm_Q hc hT.z_mem hsQ))
  have hVeq : Vt M (LB M Q B) B Z t = ⁅Q, Subgroup.zpowers s⁆ ⊔ Z := (hV s hT.s_mem hsQ).symm
  set x := z * s * z⁻¹ with hx
  have hxM : x ∈ M := by
    have hsM : s ∈ M := hc.Rt_le_M t (((hZ0 s).mp hT.s_mem).1)
    exact M.mul_mem (M.mul_mem hT.z_mem hsM) (M.inv_mem hT.z_mem)
  have hxQ : ∀ a ∈ Q, x * a * x⁻¹ ∈ Q := fun a ha => norm_Q hc hxM ha
  have hxZ : ∀ a ∈ Z, x * a * x⁻¹ ∈ Z := fun a ha =>
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Z_normal.2 hxM) a).mp ha
  have hQQ : ∀ a ∈ Q, ∀ b ∈ Q, ⁅a, b⁆ ∈ Z := fun a ha b hb =>
    hc.hyp.toHyp79.comm_mem_V ha hb
  have hZV : Z ≤ Vt M (LB M Q B) B Z t := sec39_Z_le_Vt
  have hfw : ∀ v ∈ Vt M (LB M Q B) B Z t, x * v * x⁻¹ ∈ Vt M (LB M Q B) B Z t := by
    intro v hv
    have hle : (⁅Q, Subgroup.zpowers s⁆ ⊔ Z : Subgroup G) ≤
        (Vt M (LB M Q B) B Z t).comap (MulAut.conj x).toMonoidHom := by
      refine sup_le ?_ ?_
      · rw [Subgroup.commutator_le]
        intro a ha g hg
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
        show x * ⁅a, s ^ k⁆ * x⁻¹ ∈ Vt M (LB M Q B) B Z t
        have hsk : s ^ k ∈ Z0 := zpow_mem hT.s_mem k
        have hqk : ⁅x, s ^ k⁆ ∈ Q := hT.comm _ hsk
        set qk := ⁅x, s ^ k⁆ with hqkdef
        have e1 : x * s ^ k * x⁻¹ = qk * s ^ k := by
          simp only [hqkdef, commutatorElement_def]; group
        have e2 : x * ⁅a, s ^ k⁆ * x⁻¹ = ⁅x * a * x⁻¹, qk * s ^ k⁆ := by
          rw [← e1]; simp only [commutatorElement_def]; group
        have e3 : ⁅x * a * x⁻¹, qk * s ^ k⁆ =
            ⁅x * a * x⁻¹, qk⁆ * (qk * ⁅x * a * x⁻¹, s ^ k⁆ * qk⁻¹) := by
          simp only [commutatorElement_def]; group
        rw [e2, e3]
        refine (Vt M (LB M Q B) B Z t).mul_mem (hZV (hQQ _ (hxQ a ha) _ hqk)) ?_
        have hc2 : ⁅x * a * x⁻¹, s ^ k⁆ ∈ Vt M (LB M Q B) B Z t := by
          rw [hVeq]
          exact Subgroup.mem_sup_left (Subgroup.commutator_mem_commutator (hxQ a ha) hg)
        have hVQ : Vt M (LB M Q B) B Z t ≤ Q := hc.Vt_le_Q t
        have e4 : qk * ⁅x * a * x⁻¹, s ^ k⁆ * qk⁻¹ = ⁅qk, ⁅x * a * x⁻¹, s ^ k⁆⁆ *
            ⁅x * a * x⁻¹, s ^ k⁆ := by
          simp only [commutatorElement_def]; group
        rw [e4]
        exact (Vt M (LB M Q B) B Z t).mul_mem (hZV (hQQ _ hqk _ (hVQ hc2))) hc2
      · intro ζ hζ
        show x * ζ * x⁻¹ ∈ Vt M (LB M Q B) B Z t
        exact hZV (hxZ ζ hζ)
    exact hle (hVeq ▸ hv)
  refine Subgroup.eq_of_le_of_card_ge ?_ (by rw [card_conjSubgroup])
  intro y hy
  have hy' : x⁻¹ * y * x ∈ Vt M (LB M Q B) B Z t := mem_conjSubgroup.mp hy
  have := hfw _ hy'
  simpa [mul_assoc] using this


theorem conj_Rt_of_one (h1 : Step93OneStatement) {hc : Ctx M Q Z B} {n : ℕ} {t : G}
    (hs : Sec9Hyp hc n t) {r : G} (hr : Sec7A hc t r) {Z0 : Subgroup G}
    (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q) (hsc : StronglyClosedMod M Z0 (LB M Q B))
    {x : G} (hxM : x ∈ M)
    (hxV : conjSubgroup x (Vt M (LB M Q B) B Z t) = Vt M (LB M Q B) B Z t) :
    conjSubgroup x (Rt M (LB M Q B) t) = Rt M (LB M Q B) t := by
  classical
  have ht : t ∈ LB M Q B := hs.mem
  have hrR : r ∈ Rt M (LB M Q B) t := hr.mem
  have hrM : r ∈ M := hc.Rt_le_M t hrR
  have hBV : B ≤ Vt M (LB M Q B) B Z t := hc.B_le_Vt ht
  have hZV : Z ≤ Vt M (LB M Q B) B Z t := sec39_Z_le_Vt
  have hRnorm : ∀ ρ ∈ Rt M (LB M Q B) t, conjSubgroup ρ (Rt M (LB M Q B) t) =
      Rt M (LB M Q B) t := fun ρ hρ =>
    conjSubgroup_eq_self_iff.mpr (Subgroup.le_normalizer hρ)
  have hLR : LB M Q B ≤ Rt M (LB M Q B) t := le_Rt (M := M) (LB M Q B) ht
  have hkey : ∀ m ∈ M, conjSubgroup m B ⊔ Z ≤ Vt M (LB M Q B) B Z t →
      conjSubgroup m (LB M Q B) ≤ Rt M (LB M Q B) t := by
    intro m hm hmV
    obtain ⟨ρ, hρ, hρBZ⟩ := h1 G M Q Z B hc n t hs r hr Z0 hZ0 hsc m hm hmV
    have hρM : ρ ∈ M := hc.Rt_le_M t hρ
    rw [hc.conj_LB_eq_of_conj_BZ hm hρM hρBZ]
    calc conjSubgroup ρ (LB M Q B) ≤ conjSubgroup ρ (Rt M (LB M Q B) t) := by
          intro y hy
          rw [mem_conjSubgroup] at hy ⊢
          exact hLR hy
      _ = Rt M (LB M Q B) t := hRnorm ρ hρ
  have hxVn : x ∈ Subgroup.normalizer (Vt M (LB M Q B) B Z t : Set G) :=
    conjSubgroup_eq_self_iff.mp hxV
  have hBm : ∀ m ∈ M, (∀ b ∈ B, m * b * m⁻¹ ∈ Vt M (LB M Q B) B Z t) →
      conjSubgroup m B ⊔ Z ≤ Vt M (LB M Q B) B Z t := by
    intro m hm hb
    refine sup_le (fun y hy => ?_) hZV
    rw [mem_conjSubgroup] at hy
    have := hb _ hy
    simpa [mul_assoc] using this
  have h1x : conjSubgroup x (LB M Q B) ≤ Rt M (LB M Q B) t := hkey x hxM (hBm x hxM (fun b hb =>
    (Subgroup.mem_normalizer_iff.mp hxVn b).mp (hBV hb)))
  have hxr : x * r ∈ M := M.mul_mem hxM hrM
  have h2x : conjSubgroup (x * r) (LB M Q B) ≤ Rt M (LB M Q B) t := hkey (x * r) hxr
    (hBm (x * r) hxr (fun b hb => by
      have h1' := (Subgroup.mem_normalizer_iff.mp (hc.Rt_normalizes_Vt ht hrR) b).mp (hBV hb)
      have h2' := (Subgroup.mem_normalizer_iff.mp hxVn _).mp h1'
      simpa [mul_assoc] using h2'))
  have hRgen := hr.gen
  have hle : conjSubgroup x (Rt M (LB M Q B) t) ≤ Rt M (LB M Q B) t := by
    have e : conjSubgroup x (Rt M (LB M Q B) t) =
        conjSubgroup x (LB M Q B) ⊔ conjSubgroup (x * r) (LB M Q B) := by
      conv_lhs => rw [hRgen]
      rw [hc.LB_conj hrM, conjSubgroup_mul]
      unfold conjSubgroup
      rw [Subgroup.map_sup]
    rw [e]
    exact sup_le h1x h2x
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [card_conjSubgroup])

theorem false_of_swap (h92 : Stroth92Statement) (hNon : Step92NontrivStatement)
    {hc : Ctx M Q Z B} {n : ℕ} {t : G} (hs : Sec9Hyp hc n t) {x : G} (hxM : x ∈ M)
    (hxV : conjSubgroup x (Vt M (LB M Q B) B Z t) = Vt M (LB M Q B) B Z t)
    (hnormR : conjSubgroup x (Rt M (LB M Q B) t) = Rt M (LB M Q B) t)
    (hswap : ∀ R₀ : Subgroup G, hc.CN t ≤ R₀ → R₀ ≤ Rt M (LB M Q B) t →
      (∀ ρ ∈ Rt M (LB M Q B) t, conjSubgroup ρ R₀ = R₀) → R₀ ≠ hc.CN t →
      R₀ ≠ Rt M (LB M Q B) t → conjSubgroup x R₀ ≠ R₀)
    (hx₀ : ∃ x₀ ∈ LB M Q B, x₀ ∉ hc.CN t ∧
      ∀ w ∈ Wt Q (Vt M (LB M Q B) B Z t), ⁅x₀, w⁆ ∈ Vt M (LB M Q B) B Z t) : False := by
  classical
  obtain ⟨x₀, hx₀L, hx₀N, hx₀W⟩ := hx₀
  have ht : t ∈ LB M Q B := hs.mem
  have hx₀R : x₀ ∈ Rt M (LB M Q B) t := le_Rt (M := M) (LB M Q B) ht hx₀L
  obtain ⟨⟨Y, hdp, hsl⟩, hR₀W⟩ := h92 G M Q Z B hc n t hs (Vt M (LB M Q B) B Z t)
    (Wt Q (Vt M (LB M Q B) B Z t)) rfl rfl x₀ hx₀L hx₀N hx₀W
  obtain ⟨hQR₀, hR₀R, hQY, hYR, hR₀Y, hR₀Y', hcomm⟩ := hdp
  have hxVn : x ∈ Subgroup.normalizer (Vt M (LB M Q B) B Z t : Set G) :=
    conjSubgroup_eq_self_iff.mp hxV
  have hxV1 : ∀ v ∈ Vt M (LB M Q B) B Z t, x * v * x⁻¹ ∈ Vt M (LB M Q B) B Z t := fun v hv =>
    (Subgroup.mem_normalizer_iff.mp hxVn v).mp hv
  have hxV2 : ∀ v ∈ Vt M (LB M Q B) B Z t, x⁻¹ * v * x ∈ Vt M (LB M Q B) B Z t := fun v hv => by
    have := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer _).inv_mem hxVn) v).mp hv
    simpa using this
  have hxW2 : ∀ w ∈ Wt Q (Vt M (LB M Q B) B Z t), x⁻¹ * w * x ∈ Wt Q (Vt M (LB M Q B) B Z t) := by
    intro w hw
    refine ⟨?_, Subgroup.mem_centralizer_iff.mpr fun v hv => ?_⟩
    · have := norm_Q hc (M.inv_mem hxM) hw.1
      simpa using this
    · have h1 := Subgroup.mem_centralizer_iff.mp hw.2 (x * v * x⁻¹) (hxV1 v hv)
      have e1 : x⁻¹ * (x * v * x⁻¹ * w) * x = v * (x⁻¹ * w * x) := by group
      have e2 : x⁻¹ * (w * (x * v * x⁻¹)) * x = (x⁻¹ * w * x) * v := by group
      rw [← e1, ← e2, h1]
  have hnormR₀ : ∀ ρ ∈ Rt M (LB M Q B) t, ∀ a ∈ Sec9R0 hc t x₀, ρ * a * ρ⁻¹ ∈ Sec9R0 hc t x₀ := by
    intro ρ hρ a ha
    have hgen : ∀ ρ' ∈ Rt M (LB M Q B) t, ρ' * x₀ * ρ'⁻¹ ∈ Sec9R0 hc t x₀ := fun ρ' hρ' =>
      Subgroup.mem_sup_right (Subgroup.mem_iSup_of_mem ρ'
        (Subgroup.mem_iSup_of_mem hρ' (Subgroup.mem_zpowers _)))
    have hle : Sec9R0 hc t x₀ ≤ (Sec9R0 hc t x₀).comap (MulAut.conj ρ).toMonoidHom := by
      refine sup_le ?_ (iSup₂_le fun ρ' hρ' => ?_)
      · intro a ha
        exact CN_le_Sec9R0 hc t x₀ (conj_mem_CN hc ht hρ ha)
      · rw [Subgroup.zpowers_le]
        show ρ * (ρ' * x₀ * ρ'⁻¹) * ρ⁻¹ ∈ Sec9R0 hc t x₀
        have := hgen (ρ * ρ') ((Rt M (LB M Q B) t).mul_mem hρ hρ')
        simpa [mul_assoc] using this
    exact hle ha
  have hR₀norm : ∀ ρ ∈ Rt M (LB M Q B) t, conjSubgroup ρ (Sec9R0 hc t x₀) = Sec9R0 hc t x₀ :=
    fun ρ hρ => conjSubgroup_eq_self_iff.mpr (mem_normalizer_of (hnormR₀ ρ hρ) (fun a ha => by
      have := hnormR₀ ρ⁻¹ ((Rt M (LB M Q B) t).inv_mem hρ) a ha
      simpa using this))
  have hR₀R' : Sec9R0 hc t x₀ ≠ Rt M (LB M Q B) t := by
    intro h
    have hYQ : Y ≤ Q := by
      intro y hy
      have : y ∈ Sec9R0 hc t x₀ ⊓ Y := ⟨h ▸ hYR hy, hy⟩
      rwa [hR₀Y'] at this
    obtain ⟨hNm, hSL⟩ := hsl
    have hq4 : 4 ≤ Nat.card Z := hc.hyp.q4
    have hq2 : ∃ s : ℕ, Nat.card Z = 2 ^ s := by
      obtain ⟨e, -, he, -⟩ := hc.hyp.cp
      exact ⟨e, he⟩
    obtain ⟨-, hsim⟩ := HS9.isSLModel_two_data hq4 hq2 hSL
    have hsub : Q.subgroupOf Y = ⊤ := Subgroup.subgroupOf_eq_top.mpr hYQ
    have : Subsingleton (↥Y ⧸ Q.subgroupOf Y) := by
      rw [hsub]; exact QuotientGroup.subsingleton_quotient_top
    exact hsim.1.exists_pair_ne.elim fun a hb => hb.elim fun b hab => hab (Subsingleton.elim a b)
  have hNR₀ : hc.CN t ≤ Sec9R0 hc t x₀ := CN_le_Sec9R0 hc t x₀
  have hR₀N : Sec9R0 hc t x₀ ≠ hc.CN t := fun h => hx₀N (h ▸ mem_Sec9R0 hc t hx₀R)
  have hCR : CWV hc t ht ≤ Rt M (LB M Q B) t := fun a ha => ha.1
  have hR₀C : Sec9R0 hc t x₀ ≤ CWV hc t ht := fun a ha => ⟨hR₀R ha, hR₀W a ha⟩
  have hCnorm1 : ∀ ρ ∈ Rt M (LB M Q B) t, ∀ a ∈ CWV hc t ht, ρ * a * ρ⁻¹ ∈ CWV hc t ht := by
    intro ρ hρ a ha
    refine ⟨(Rt M (LB M Q B) t).mul_mem ((Rt M (LB M Q B) t).mul_mem hρ ha.1)
      ((Rt M (LB M Q B) t).inv_mem hρ), fun w hw => ?_⟩
    have hw' : ρ⁻¹ * w * ρ ∈ Wt Q (Vt M (LB M Q B) B Z t) := by
      have := sec9_conj_mem_Wt hc ht ((Rt M (LB M Q B) t).inv_mem hρ) hw
      simpa using this
    have e : ⁅ρ * a * ρ⁻¹, w⁆ = ρ * ⁅a, ρ⁻¹ * w * ρ⁆ * ρ⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp (hc.Rt_normalizes_Vt ht hρ) _).mp (ha.2 _ hw')
  have hCnorm : Rt M (LB M Q B) t ≤ Subgroup.normalizer (CWV hc t ht : Set G) := fun ρ hρ =>
    mem_normalizer_of (hCnorm1 ρ hρ) (fun a ha => by
      have := hCnorm1 ρ⁻¹ ((Rt M (LB M Q B) t).inv_mem hρ) a ha
      simpa using this)
  have hxR₀C : conjSubgroup x (Sec9R0 hc t x₀) ≤ CWV hc t ht := by
    intro a' ha'
    have ha : x⁻¹ * a' * x ∈ Sec9R0 hc t x₀ := mem_conjSubgroup.mp ha'
    refine ⟨?_, fun w hw => ?_⟩
    · have : a' ∈ conjSubgroup x (Rt M (LB M Q B) t) := mem_conjSubgroup.mpr (hR₀R ha)
      rwa [hnormR] at this
    · have e : ⁅a', w⁆ = x * ⁅x⁻¹ * a' * x, x⁻¹ * w * x⁆ * x⁻¹ := by
        simp only [commutatorElement_def]; group
      rw [e]
      exact hxV1 _ (hR₀W _ ha _ (hxW2 w hw))
  have hXYn : Sec9R0 hc t x₀ ≤ Subgroup.normalizer (Y : Set G) := fun a ha =>
    mem_normalizer_of (fun h hh => by
      have e : a * h * a⁻¹ = ⁅a, h⁆ * h := by simp only [commutatorElement_def]; group
      rw [e]
      exact Y.mul_mem (hQY (hcomm a ha h hh)) hh) (fun h hh => by
      have e : a⁻¹ * h * a = ⁅a⁻¹, h⁆ * h := by simp only [commutatorElement_def]; group
      rw [e]
      exact Y.mul_mem (hQY (hcomm a⁻¹ ((Sec9R0 hc t x₀).inv_mem ha) h hh)) hh)
  have hsimple : ∃ _ : (Q.subgroupOf Y).Normal, IsSimpleGroup (↥Y ⧸ Q.subgroupOf Y) := by
    obtain ⟨hNm, hSL⟩ := hsl
    have hq4 : 4 ≤ Nat.card Z := hc.hyp.q4
    have hq2 : ∃ s : ℕ, Nat.card Z = 2 ^ s := by
      obtain ⟨e, -, he, -⟩ := hc.hyp.cp
      exact ⟨e, he⟩
    exact ⟨hNm, (HS9.isSLModel_two_data hq4 hq2 hSL).2⟩
  rcases eq_or_eq_of_simple hR₀R hYR hR₀Y hR₀Y' hXYn hCR hCnorm hR₀C hsimple with h | h
  · have hxR₀ : conjSubgroup x (Sec9R0 hc t x₀) = Sec9R0 hc t x₀ :=
      Subgroup.eq_of_le_of_card_ge (h ▸ hxR₀C) (by rw [card_conjSubgroup])
    exact hswap _ hNR₀ hR₀R hR₀norm hR₀N hR₀R' hxR₀
  · obtain ⟨ρ, hρ, w, hw, hρw⟩ := hNon G M Q Z B hc n t hs (Vt M (LB M Q B) B Z t)
      (Wt Q (Vt M (LB M Q B) B Z t)) rfl rfl
    have hρC : ρ ∈ CWV hc t ht := by rw [h]; exact hρ
    exact hρw (hρC.2 w hw)

end HS93

theorem step93Vanish_of_swap (h92 : Stroth92Statement) (hNon : Step92NontrivStatement)
    (hGe5 : Sec9NGeFiveStatement) (hN5 : Sec95N5Statement) (hN6 : Sec95N6Statement)
    (hCentre : Step95CentreStatement) (h1 : Step93OneStatement)
    (hSwap : Step93VanishSwapStatement) (hCount : Step93VanishCountStatement) :
    Step93VanishStatement := by
  intro G _ _ M Q Z B hc n t hs r hr Z0 hZ0 hsc s z hT v hv
  by_contra hne
  have hne' : ∃ v ∈ Vt M (LB M Q B) B Z t, ⁅z * s * z⁻¹, v⁆ ∉ Z := ⟨v, hv, hne⟩
  have hn6 : n ≤ 6 := hCount G M Q Z B hc n t hs r hr Z0 hZ0 hsc s z hT hne'
  have hn5 : 5 ≤ n := hGe5 G M Q Z B hc n t hs
  have hsM : s ∈ M := hc.Rt_le_M t (((hZ0 s).mp hT.s_mem).1)
  have hxM : z * s * z⁻¹ ∈ M := M.mul_mem (M.mul_mem hT.z_mem hsM) (M.inv_mem hT.z_mem)
  have hxV := HS93.conj_Vt_of_centre hCentre hs hZ0 hT
  have hnormR := HS93.conj_Rt_of_one h1 hs hr hZ0 hsc hxM hxV
  have hx₀ : ∃ x₀ ∈ LB M Q B, x₀ ∉ hc.CN t ∧
      ∀ w ∈ Wt Q (Vt M (LB M Q B) B Z t), ⁅x₀, w⁆ ∈ Vt M (LB M Q B) B Z t := by
    rcases (by omega : n = 5 ∨ n = 6) with h | h
    · exact hN5 G M Q Z B hc n t hs h
    · exact hN6 G M Q Z B hc n t hs h
  exact HS93.false_of_swap h92 hNon hs hxM hxV hnormR
    (hSwap G M Q Z B hc n t hs r hr Z0 hZ0 hsc s z hT hne') hx₀

end CFSG.RankThree.GF2n.Stroth80
