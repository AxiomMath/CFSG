module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.H13.U3HullAbs

public section

namespace CFSG.Quasithin.H13.L32A

variable {G : Type} [Group G] [Finite G]

theorem ncard_conj_le {I H : Subgroup G} {z : G}
    (hHz : ∀ h ∈ H, h * z * h⁻¹ = z) :
    {w : G | ∃ g ∈ I, g * z * g⁻¹ = w}.ncard ≤ H.relIndex I := by
  let _ : MulAction ↥I G := MulAction.compHom G ((MulAut.conj : G →* MulAut G).comp I.subtype)
  have hsmul : ∀ (x : ↥I) (w : G), x • w = (x : G) * w * (x : G)⁻¹ := fun _ _ => rfl
  have horb : MulAction.orbit ↥I z = {w : G | ∃ g ∈ I, g * z * g⁻¹ = w} := by
    ext w
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x, x.2, (hsmul x z).symm⟩
    · rintro ⟨g, hg, rfl⟩
      exact ⟨⟨g, hg⟩, hsmul _ z⟩
  have hle : H.subgroupOf I ≤ MulAction.stabilizer ↥I z := by
    intro x hx
    rw [MulAction.mem_stabilizer_iff, hsmul]
    exact hHz x (Subgroup.mem_subgroupOf.mp hx)
  have hidx := MulAction.index_stabilizer ↥I z
  rw [horb] at hidx
  rw [← hidx]
  exact Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
    (Subgroup.index_dvd_of_le hle)

theorem false_of_ncard_le_seven {I : Subgroup G} {z c x y : G} (hxI : x ∈ I) (hyI : y ∈ I)
    (hx3 : x ^ 3 = 1) (hxz : x * z * x⁻¹ = z) (hyz : y * z * y⁻¹ = c)
    (hyc : y * c * y⁻¹ = z * c) (hz1 : z ≠ 1) (hzz : z * z = 1) (hcc : c * c = 1)
    (hzc : z * c = c * z) {V : Subgroup G} (hzV : z ∈ V) (hcV : c ∉ V)
    (hxV : x ∈ Subgroup.normalizer (V : Set G)) (hd : c⁻¹ * (x * c * x⁻¹) ∈ V)
    (hd1 : c⁻¹ * (x * c * x⁻¹) ≠ 1) (hdz : c⁻¹ * (x * c * x⁻¹) ≠ z)
    (h7 : {w : G | ∃ g ∈ I, g * z * g⁻¹ = w}.ncard ≤ 7) : False := by
  classical
  set O := {w : G | ∃ g ∈ I, g * z * g⁻¹ = w} with hO
  set d₁ := c⁻¹ * (x * c * x⁻¹) with hd₁
  set d₂ := c⁻¹ * (x⁻¹ * c * x) with hd₂
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hzz
  have hci : c⁻¹ = c := inv_eq_of_mul_eq_one_right hcc
  have hxzc : x * z = z * x := by
    calc x * z = x * z * x⁻¹ * x := by group
      _ = z * x := by rw [hxz]
  have hxinvz : x⁻¹ * z * x = z := by
    calc x⁻¹ * z * x = x⁻¹ * (x * z * x⁻¹) * x := by rw [hxz]
      _ = z := by group
  have hx2 : x * x = x⁻¹ := by
    calc x * x = x ^ 3 * x⁻¹ := by rw [pow_three]; group
      _ = x⁻¹ := by rw [hx3, one_mul]
  have hc2 : x * c * x⁻¹ = c * d₁ := by rw [hd₁]; group
  have hc3 : x⁻¹ * c * x = c * d₂ := by rw [hd₂]; group
  have hd2e : d₂ = x⁻¹ * d₁⁻¹ * x := by rw [hd₂, hd₁]; group
  have hd2V : d₂ ∈ V := by
    rw [hd2e]
    have := (Subgroup.mem_normalizer_iff.mp (inv_mem hxV) d₁⁻¹).mp (inv_mem hd)
    simpa using this
  have hd21 : d₂ ≠ 1 := by
    intro e
    apply hd1
    have : d₁⁻¹ = 1 := by
      calc d₁⁻¹ = x * d₂ * x⁻¹ := by rw [hd2e]; group
        _ = 1 := by rw [e]; group
    simpa using this
  have hd2z : d₂ ≠ z := by
    intro e
    apply hdz
    have : d₁⁻¹ = z := by
      calc d₁⁻¹ = x * d₂ * x⁻¹ := by rw [hd2e]; group
        _ = z := by rw [e, hxz]
    rw [← hzi, ← this, inv_inv]
  have hconj : ∀ w : G, x * (x * w * x⁻¹) * x⁻¹ = x⁻¹ * w * x := by
    intro w
    calc x * (x * w * x⁻¹) * x⁻¹ = (x * x) * w * (x * x)⁻¹ := by group
      _ = x⁻¹ * w * x := by rw [hx2]; group
  have hd12 : d₁ ≠ d₂ := by
    intro e
    apply hd21
    have h1 : x * c * x⁻¹ = x⁻¹ * c * x := by
      calc x * c * x⁻¹ = c * d₁ := hc2
        _ = c * d₂ := by rw [e]
        _ = x⁻¹ * c * x := hc3.symm
    have h2 : x⁻¹ * c * x = c := by
      calc x⁻¹ * c * x = x * (x * c * x⁻¹) * x⁻¹ := (hconj c).symm
        _ = x * (x⁻¹ * c * x) * x⁻¹ := by rw [h1]
        _ = c := by group
    rw [hd₂, h2, inv_mul_cancel]
  have hd1z2 : d₁ ≠ z * d₂ := by
    intro e
    apply hd2z
    have h1 : x * c * x⁻¹ = z * (x⁻¹ * c * x) := by
      calc x * c * x⁻¹ = c * d₁ := hc2
        _ = c * (z * d₂) := by rw [e]
        _ = z * (c * d₂) := by rw [← mul_assoc, ← hzc, mul_assoc]
        _ = z * (x⁻¹ * c * x) := by rw [hc3]
    have h2 : x⁻¹ * c * x = z * c := by
      calc x⁻¹ * c * x = x * (x * c * x⁻¹) * x⁻¹ := (hconj c).symm
        _ = x * (z * (x⁻¹ * c * x)) * x⁻¹ := by rw [h1]
        _ = (x * z * x⁻¹) * c := by group
        _ = z * c := by rw [hxz]
    rw [hd₂, h2, hzc]
    group
  have hzd12 : z * d₁ ≠ d₂ := by
    intro e
    apply hd2z
    have h1 : z * (x * c * x⁻¹) = x⁻¹ * c * x := by
      calc z * (x * c * x⁻¹) = z * (c * d₁) := by rw [hc2]
        _ = c * (z * d₁) := by rw [← mul_assoc, hzc, mul_assoc]
        _ = c * d₂ := by rw [e]
        _ = x⁻¹ * c * x := hc3.symm
    have h2 : x⁻¹ * c * x = z * c := by
      have h3 : z * (x⁻¹ * c * x) = c := by
        calc z * (x⁻¹ * c * x) = x * (z * (x * c * x⁻¹)) * x⁻¹ := by
              rw [← hconj c]
              calc z * (x * (x * c * x⁻¹) * x⁻¹) = (x * z * x⁻¹) * (x * (x * c * x⁻¹) * x⁻¹) := by
                    rw [hxz]
                _ = x * (z * (x * c * x⁻¹)) * x⁻¹ := by group
          _ = x * (x⁻¹ * c * x) * x⁻¹ := by rw [h1]
          _ = c := by group
      calc x⁻¹ * c * x = z * (z * (x⁻¹ * c * x)) := by rw [← mul_assoc, hzz, one_mul]
        _ = z * c := by rw [h3]
    rw [hd₂, h2, hzc]
    group
  have hzd11 : z * d₁ ≠ 1 := by
    intro e
    apply hdz
    calc d₁ = z * (z * d₁) := by rw [← mul_assoc, hzz, one_mul]
      _ = z := by rw [e, mul_one]
  have hzd21 : z * d₂ ≠ 1 := by
    intro e
    apply hd2z
    calc d₂ = z * (z * d₂) := by rw [← mul_assoc, hzz, one_mul]
      _ = z := by rw [e, mul_one]
  have hOconj : ∀ g ∈ I, ∀ w ∈ O, g * w * g⁻¹ ∈ O := by
    rintro g hg w ⟨h, hh, rfl⟩
    exact ⟨g * h, mul_mem hg hh, by group⟩
  have hzO : z ∈ O := ⟨1, one_mem _, by group⟩
  have hcO : c ∈ O := ⟨y, hyI, hyz⟩
  have hzcO : z * c ∈ O := hyc ▸ hOconj y hyI c hcO
  have hc2O : x * c * x⁻¹ ∈ O := hOconj x hxI c hcO
  have hc3O : x⁻¹ * c * x ∈ O := by
    have := hOconj x⁻¹ (inv_mem hxI) c hcO
    simpa using this
  have hzc2O : z * (x * c * x⁻¹) ∈ O := by
    have e : z * (x * c * x⁻¹) = x * (z * c) * x⁻¹ := by
      rw [← mul_assoc, ← mul_assoc, ← hxzc]; group
    rw [e]
    exact hOconj x hxI _ hzcO
  have hzc3O : z * (x⁻¹ * c * x) ∈ O := by
    have e : z * (x⁻¹ * c * x) = x⁻¹ * (z * c) * x := by
      calc z * (x⁻¹ * c * x) = (x⁻¹ * z * x) * (x⁻¹ * c * x) := by rw [hxinvz]
        _ = x⁻¹ * (z * c) * x := by group
    rw [e]
    have := hOconj x⁻¹ (inv_mem hxI) _ hzcO
    simpa using this
  have hcsV : ∀ s ∈ V, c * s ∉ V := by
    intro s hs hcs
    apply hcV
    have := mul_mem hcs (inv_mem hs)
    simpa using this
  have hcsz : ∀ s ∈ V, c * s ≠ z := fun s hs e => hcsV s hs (e ▸ hzV)
  have hzdV : z * d₁ ∈ V := mul_mem hzV hd
  have hzd2V : z * d₂ ∈ V := mul_mem hzV hd2V
  have hzcs : ∀ s ∈ V, z ≠ c * s := fun s hs e => hcsz s hs e.symm
  have hcne : ∀ s, s ≠ 1 → c ≠ c * s := by
    intro s hs e
    apply hs
    have := congrArg (c⁻¹ * ·) e
    simpa using this.symm
  have hcinj : ∀ s t : G, s ≠ t → c * s ≠ c * t := fun s t h e => h (mul_left_cancel e)
  have hzne : ∀ s : G, s ≠ 1 → z ≠ z * s := by
    intro s hs e
    apply hs
    have := congrArg (z⁻¹ * ·) e
    simpa using this.symm
  have hzne' : ∀ s : G, s ≠ z * s := by
    intro s e
    apply hz1
    have := congrArg (· * s⁻¹) e
    simpa using this.symm
  have hstar : ∀ w ∈ O, w = z ∨ w = c ∨ w = c * z ∨ w = c * d₁ ∨ w = c * (z * d₁) ∨
      w = c * d₂ ∨ w = c * (z * d₂) := by
    intro w hw
    by_contra hne
    push Not at hne
    obtain ⟨h0, h1, h2, h3, h4, h5, h6⟩ := hne
    set l : List G := [w, z, c, c * z, c * d₁, c * (z * d₁), c * d₂, c * (z * d₂)] with hl
    have hnd : l.Nodup := by
      rw [hl]
      simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
        List.nodup_nil, not_false_eq_true, and_true]
      refine ⟨⟨h0, h1, h2, h3, h4, h5, h6⟩,
        ⟨by simpa using hzcs 1 (one_mem _), hzcs z hzV, hzcs d₁ hd, hzcs _ hzdV, hzcs d₂ hd2V,
          hzcs _ hzd2V⟩,
        ⟨hcne z hz1, hcne d₁ hd1, hcne _ hzd11, hcne d₂ hd21, hcne _ hzd21⟩,
        ⟨hcinj _ _ hdz.symm, hcinj _ _ (hzne d₁ hd1), hcinj _ _ hd2z.symm,
          hcinj _ _ (hzne d₂ hd21)⟩,
        ⟨hcinj _ _ (hzne' d₁), hcinj _ _ hd12, hcinj _ _ hd1z2⟩,
        ⟨hcinj _ _ hzd12, hcinj _ _ fun e => hd12 (mul_left_cancel e)⟩,
        hcinj _ _ (hzne' d₂)⟩
    have hsub : (l.toFinset : Set G) ⊆ O := by
      intro u hu
      rw [Finset.mem_coe, List.mem_toFinset, hl] at hu
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact hw
      · exact hzO
      · exact hcO
      · rw [← hzc]; exact hzcO
      · rw [← hc2]; exact hc2O
      · rw [← mul_assoc, ← hzc, mul_assoc, ← hc2]; exact hzc2O
      · rw [← hc3]; exact hc3O
      · rw [← mul_assoc, ← hzc, mul_assoc, ← hc3]; exact hzc3O
    have h8 := Set.ncard_le_ncard hsub (Set.toFinite O)
    rw [Set.ncard_coe_finset, List.toFinset_card_of_nodup hnd, hl] at h8
    simp only [List.length_cons, List.length_nil] at h8
    omega
  have hVO : ∀ s ∈ V, s ∈ O → s = z := by
    intro s hs hsO
    rcases hstar s hsO with e | e | e | e | e | e | e
    · exact e
    all_goals exfalso
    · exact hcV (e ▸ hs)
    · exact hcsV z hzV (e ▸ hs)
    · exact hcsV d₁ hd (e ▸ hs)
    · exact hcsV _ hzdV (e ▸ hs)
    · exact hcsV d₂ hd2V (e ▸ hs)
    · exact hcsV _ hzd2V (e ▸ hs)
  have hp : ∀ q ∈ O, z * q ∈ O → y * q * y⁻¹ = z ∨ y * q * y⁻¹ = z * c := by
    intro q hq hzq
    have hp1 : y * q * y⁻¹ ∈ O := hOconj y hyI q hq
    have hp2 : c * (y * q * y⁻¹) ∈ O := by
      have e : c * (y * q * y⁻¹) = y * (z * q) * y⁻¹ := by rw [← hyz]; group
      rw [e]
      exact hOconj y hyI _ hzq
    rcases hstar _ hp1 with e | e | e | e | e | e | e
    · exact Or.inl e
    · exfalso
      rw [e, hcc] at hp2
      obtain ⟨g, -, hg⟩ := hp2
      apply hz1
      calc z = g⁻¹ * (g * z * g⁻¹) * g := by group
        _ = 1 := by rw [hg]; group
    · exact Or.inr (by rw [e, hzc])
    all_goals exfalso
    · rw [e, ← mul_assoc, hcc, one_mul] at hp2
      exact hdz (hVO d₁ hd hp2)
    · rw [e, ← mul_assoc, hcc, one_mul] at hp2
      exact hzne d₁ hd1 (hVO _ hzdV hp2).symm
    · rw [e, ← mul_assoc, hcc, one_mul] at hp2
      exact hd2z (hVO d₂ hd2V hp2)
    · rw [e, ← mul_assoc, hcc, one_mul] at hp2
      exact hzne d₂ hd21 (hVO _ hzd2V hp2).symm
  have hinj : ∀ q q' : G, y * q * y⁻¹ = y * q' * y⁻¹ → q = q' :=
    fun q q' e => mul_left_cancel (mul_right_cancel e)
  have hc2ne : x * c * x⁻¹ ≠ c := by
    intro e
    apply hd1
    rw [hd₁, e, inv_mul_cancel]
  have hc23 : x * c * x⁻¹ ≠ x⁻¹ * c * x := by
    intro e
    apply hd12
    rw [hd₁, hd₂, e]
  have hc3ne : x⁻¹ * c * x ≠ c := by
    intro e
    apply hd21
    rw [hd₂, e, inv_mul_cancel]
  rcases hp _ hc2O hzc2O with e2 | e2
  · rcases hp _ hc3O hzc3O with e3 | e3
    · exact hc23 (hinj _ _ (e2.trans e3.symm))
    · exact hc3ne (hinj _ _ (e3.trans hyc.symm))
  · exact hc2ne (hinj _ _ (e2.trans hyc.symm))

end CFSG.Quasithin.H13.L32A
