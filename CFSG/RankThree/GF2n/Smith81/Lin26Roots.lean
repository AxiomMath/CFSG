module

public import CFSG.RankThree.GF2n.Smith81.LinRestModel
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80
open scoped commutatorElement Pointwise

section Roots

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem Ctx.QB_comm_mem (hc : Ctx M Q Z B) {a b : G} (ha : a ∈ QB B) (hb : b ∈ QB B) :
    ⁅a, b⁆ ∈ B := by
  obtain ⟨g, hg⟩ := hc.conj
  rw [(Ctx.QB_eq hc hg).2] at ha hb
  rw [hg]
  exact hc.hyp.toHyp79.comm_mem_conj g ha hb

theorem Ctx.B_central_QB (hc : Ctx M Q Z B) {b u : G} (hb : b ∈ B) (hu : u ∈ QB B) :
    b * u = u * b := by
  obtain ⟨g, hg⟩ := hc.conj
  rw [(Ctx.QB_eq hc hg).2, mem_conjSubgroup] at hu
  rw [hg, mem_conjSubgroup] at hb
  have h := Z_central hc.hyp hb hu
  calc b * u = g * ((g⁻¹ * b * g) * (g⁻¹ * u * g)) * g⁻¹ := by group
    _ = g * ((g⁻¹ * u * g) * (g⁻¹ * b * g)) * g⁻¹ := by rw [h]
    _ = u * b := by group

theorem Ctx.B_le_normalizer_Z (hc : Ctx M Q Z B) : B ≤ Subgroup.normalizer (Z : Set G) := by
  intro b hb
  refine Subgroup.mem_normalizer_fintype fun z hz => ?_
  have := Z_central hc.hyp hz (hc.le hb)
  have e : b * z * b⁻¹ = z := by
    calc b * z * b⁻¹ = (z * b) * b⁻¹ := by rw [← this]
      _ = z := by group
  rw [e]; exact hz

theorem Ctx.mem_sup_iff (hc : Ctx M Q Z B) {w : G} :
    w ∈ Z ⊔ B ↔ ∃ z ∈ Z, ∃ b ∈ B, w = z * b := by
  have h : ((Z ⊔ B : Subgroup G) : Set G) = (Z : Set G) * (B : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left Z B (Ctx.B_le_normalizer_Z hc)
  constructor
  · intro hw
    have hw' : w ∈ ((Z ⊔ B : Subgroup G) : Set G) := hw
    rw [h] at hw'
    obtain ⟨z, hz, b, hb, rfl⟩ := hw'
    exact ⟨z, hz, b, hb, rfl⟩
  · rintro ⟨z, hz, b, hb, rfl⟩
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hz) (Subgroup.mem_sup_right hb)

theorem Ctx.Q_le_normalizer_ZB (hc : Ctx M Q Z B) :
    Q ≤ Subgroup.normalizer ((Z ⊔ B : Subgroup G) : Set G) := by
  intro q hq
  refine Subgroup.mem_normalizer_fintype fun w hw => ?_
  obtain ⟨z, hz, b, hb, rfl⟩ := (Ctx.mem_sup_iff hc).mp hw
  have hzq : z * q = q * z := Z_central hc.hyp hz hq
  have hc1 : ⁅q, b⁆ ∈ Z := comm_mem_Z hc.hyp hq (hc.le hb)
  have e : q * (z * b) * q⁻¹ = z * ⁅q, b⁆ * b := by
    have : q * z * q⁻¹ = z := by
      calc q * z * q⁻¹ = (z * q) * q⁻¹ := by rw [← hzq]
        _ = z := by group
    calc q * (z * b) * q⁻¹ = (q * z * q⁻¹) * (q * b * q⁻¹) := by group
      _ = z * (⁅q, b⁆ * b) := by rw [this]; simp only [commutatorElement_def]; group
      _ = z * ⁅q, b⁆ * b := by group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_left hz)
    (Subgroup.mem_sup_left hc1)) (Subgroup.mem_sup_right hb)

theorem Ctx.QB_le_normalizer_ZB (hc : Ctx M Q Z B) :
    QB B ≤ Subgroup.normalizer ((Z ⊔ B : Subgroup G) : Set G) := by
  intro u hu
  refine Subgroup.mem_normalizer_fintype fun w hw => ?_
  obtain ⟨z, hz, b, hb, rfl⟩ := (Ctx.mem_sup_iff hc).mp hw
  have hzu : z ∈ QB B := (Ctx.Z_le_QB hc).1 hz
  have hc1 : ⁅u, z⁆ ∈ B := Ctx.QB_comm_mem hc hu hzu
  have hbu : b * u = u * b := Ctx.B_central_QB hc hb hu
  have e : u * (z * b) * u⁻¹ = ⁅u, z⁆ * z * b := by
    have : u * b * u⁻¹ = b := by
      calc u * b * u⁻¹ = (b * u) * u⁻¹ := by rw [← hbu]
        _ = b := by group
    calc u * (z * b) * u⁻¹ = (u * z * u⁻¹) * (u * b * u⁻¹) := by group
      _ = (⁅u, z⁆ * z) * b := by rw [this]; simp only [commutatorElement_def]; group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_right hc1)
    (Subgroup.mem_sup_left hz)) (Subgroup.mem_sup_right hb)

theorem Ctx.sup_QB_le_normalizer_ZB (hc : Ctx M Q Z B) :
    Q ⊔ QB B ≤ Subgroup.normalizer ((Z ⊔ B : Subgroup G) : Set G) :=
  sup_le (Ctx.Q_le_normalizer_ZB hc) (Ctx.QB_le_normalizer_ZB hc)

theorem Ctx.sup_QB_comm_inf_mem (hc : Ctx M Q Z B) {g d : G} (hg : g ∈ Q ⊔ QB B)
    (hd : d ∈ Q ⊓ QB B) : ⁅g, d⁆ ∈ Z ⊔ B := by
  have hBQB : B ≤ QB B := by
    obtain ⟨g, hg⟩ := hc.conj
    rw [(Ctx.QB_eq hc hg).2, hg]
    exact Subgroup.map_mono hc.Z_le_Q
  let T : Subgroup G :=
    { carrier := {g | g ∈ Subgroup.normalizer ((Z ⊔ B : Subgroup G) : Set G) ∧
        ∀ d ∈ Q ⊓ QB B, ⁅g, d⁆ ∈ Z ⊔ B}
      mul_mem' := by
        rintro a b ⟨haN, ha⟩ ⟨hbN, hb⟩
        refine ⟨Subgroup.mul_mem _ haN hbN, fun d hd => ?_⟩
        have e : ⁅a * b, d⁆ = a * ⁅b, d⁆ * a⁻¹ * ⁅a, d⁆ := by
          simp only [commutatorElement_def]; group
        rw [e]
        exact (Z ⊔ B).mul_mem ((Subgroup.mem_normalizer_iff.mp haN _).mp (hb d hd)) (ha d hd)
      one_mem' := ⟨Subgroup.one_mem _, fun d _ => by
        simp only [commutatorElement_def]; simpa using (Z ⊔ B).one_mem⟩
      inv_mem' := by
        rintro a ⟨haN, ha⟩
        refine ⟨Subgroup.inv_mem _ haN, fun d hd => ?_⟩
        have e : ⁅a⁻¹, d⁆ = a⁻¹ * ⁅a, d⁆⁻¹ * a⁻¹⁻¹ := by
          simp only [commutatorElement_def]; group
        rw [e]
        exact (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ haN) _).mp
          ((Z ⊔ B).inv_mem (ha d hd)) }
  have hQT : Q ≤ T := fun q hq =>
    ⟨Ctx.Q_le_normalizer_ZB hc hq, fun d hd =>
      Subgroup.mem_sup_left (comm_mem_Z hc.hyp hq hd.1)⟩
  have hBT : QB B ≤ T := fun u hu =>
    ⟨Ctx.QB_le_normalizer_ZB hc hu, fun d hd =>
      Subgroup.mem_sup_right (Ctx.QB_comm_mem hc hu hd.2)⟩
  exact (sup_le hQT hBT hg).2 d hd

end Roots

section RootsModel

variable {G : Type} [Group G] [Finite G] {M Q Z : Subgroup G}
  {n : ℕ} {V₁ V₂ : Subgroup G}

theorem RestModel.exists_root (R : RestModel M Q Z n V₁ V₂) (hn : 1 ≤ n)
    (hcl : ∀ v ∈ V₂, v ≠ 1 → InZClass Z v) :
    ∃ Y : Subgroup G, Ctx M Q Z Y ∧ Y ≤ V₂ := by
  have H := R.hyp
  obtain ⟨v, hvV, hvZ⟩ : ∃ v ∈ V₂, v ∉ Z := by
    by_contra hcon
    push Not at hcon
    have hsub : Subsingleton ↥R.W₂ := ⟨fun a b => by
      obtain ⟨x, hx, hxQ, hxa⟩ := (R.memW₂ a.1).mp a.2
      obtain ⟨y, hy, hyQ, hyb⟩ := (R.memW₂ b.1).mp b.2
      apply Subtype.ext
      rw [← hxa, ← hyb, (R.M₀.π_ker x hxQ).mpr (hcon x hx),
        (R.M₀.π_ker y hyQ).mpr (hcon y hy)]⟩
    have h1 : Nat.card ↥R.W₂ = 1 :=
      Nat.card_eq_one_iff_unique.mpr ⟨hsub, ⟨⟨0, Submodule.zero_mem _⟩⟩⟩
    rw [R.card_W₂] at h1
    have h4 := H.q4
    have h5 : 1 < Nat.card Z ^ n := Nat.one_lt_pow (by omega) (by omega)
    omega
  have hvQ : v ∈ Q := R.V₂Q hvV
  have hv1 : v ≠ 1 := fun h => hvZ (h ▸ Z.one_mem)
  obtain ⟨g, z, hz, -, hvg⟩ := hcl v hvV hv1
  obtain ⟨g', hg'Q, hvg'⟩ := stroth_2_6 H hvQ hvZ ⟨g, z, hz, hvg⟩
  have hYZ : conjSubgroup g' Z ≠ Z := fun h => hvZ (h ▸ hvg')
  refine ⟨conjSubgroup g' Z, ⟨H, ⟨g', rfl⟩, hg'Q, hYZ⟩, ?_⟩
  obtain ⟨e, he0, he⟩ := R.gm.line g' hYZ hg'Q
  have hπv : R.M₀.π v ∈ R.M₀.img (conjSubgroup g' Z) := R.M₀.pi_mem_img hvg' hvQ
  obtain ⟨t, ht⟩ := (he _).mp hπv
  have hπv0 : R.M₀.π v ≠ 0 := fun h => hvZ ((R.M₀.π_ker v hvQ).mp h)
  have ht0 : t ≠ 0 := fun h => hπv0 (by rw [ht, h, zero_smul])
  have heW : e ∈ R.W₂ := by
    have : e = t⁻¹ • R.M₀.π v := by rw [ht, smul_smul, inv_mul_cancel₀ ht0, one_smul]
    rw [this]
    exact R.W₂.smul_mem _ ((R.memW₂ _).mpr (R.M₀.pi_mem_img hvV hvQ))
  intro y hy
  have hyQ : y ∈ Q := hg'Q hy
  have hy' : R.M₀.π y ∈ R.M₀.img (conjSubgroup g' Z) := R.M₀.pi_mem_img hy hyQ
  obtain ⟨s, hs⟩ := (he _).mp hy'
  have hW : R.M₀.π y ∈ R.W₂ := by rw [hs]; exact R.W₂.smul_mem s heW
  exact (R.M₀.mem_img_iff R.ZV₂ hyQ).mp ((R.memW₂ _).mp hW)

end RootsModel

end CFSG.RankThree.GF2n.Smith81
