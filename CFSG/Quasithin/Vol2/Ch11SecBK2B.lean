module

public import CFSG.Quasithin.Vol2.Ch11G2Q8AutV
public import CFSG.Quasithin.Vol2.Ch11SecA12Out2
public import CFSG.Quasithin.Vol2.Ch10SecABasicAut
public import CFSG.Quasithin.Vol2.Ch11SecA02Eight
public import CFSG.Quasithin.Vol2.KGNatSL3Par
public import CFSG.Quasithin.Vol2.KGNatSp4Std

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13
open CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall
open scoped IsMulCommutative

namespace BK2

section Lin

variable {D : FFModel} {K M : Type} [Field K] [Finite K] [CharP K 2] [AddCommGroup M]
  [Module K M] {W : Type*} [CommGroup W] {LM : KGNat.LinModel D K M} {H : Subgroup (MulAut W)}
  {Z : Subgroup W} {π : D.Gam →* ↥H} {f : W → M}

theorem eq_one_of_commute_two (hf : KGNat.IsCoord LM H Z π f)
    (hcomm : ∀ T : M →+ M, (∀ (γ : D.Gam) (x : M), T (LM.lin γ x) = LM.lin γ (T x)) →
      ∃ c : K, ∀ x, T x = c • x)
    {x₀ : M} (hx₀ : x₀ ≠ 0) (hW : commV H = ⊤) (hZ : Z ≤ fixV H) {τ : MulAut W}
    (hτZ : ∀ z ∈ Z, τ z ∈ Z) (hτH : ∀ h ∈ H, τ * h = h * τ) {k : ℕ} (hτ2 : τ ^ 2 ^ k = 1) :
    τ = 1 := by
  have hTf : ∀ w, hf.autMap τ hτZ (f w) = f (τ w) := hf.autMap_apply τ hτZ
  obtain ⟨c, hc⟩ := hcomm (hf.autMap τ hτZ) fun γ x => hf.autMap_lin τ hτZ γ γ (by
    rw [hτH _ (π γ).2, mul_inv_cancel_right]) x
  have hpow : ∀ j : ℕ, ∀ w, f ((τ ^ j) w) = c ^ j • f w := by
    intro j
    induction j with
    | zero => intro w; rw [pow_zero, pow_zero, one_smul, MulAut.one_apply]
    | succ j ih =>
      intro w
      rw [pow_succ', MulAut.mul_apply, ← hTf, hc, ih, smul_smul, pow_succ']
  obtain ⟨w₀, hw₀⟩ := hf.surj x₀
  have hc1 : c = 1 := by
    have h1 := hpow (2 ^ k) w₀
    rw [hτ2, MulAut.one_apply, hw₀] at h1
    have h2 : (c ^ 2 ^ k - 1) • x₀ = 0 := by rw [sub_smul, ← h1, one_smul, sub_self]
    exact KGNat.eq_one_of_pow_two_pow
      (sub_eq_zero.mp ((smul_eq_zero.mp h2).resolve_right hx₀))
  refine KGNat.eq_one_of_commV hW hτH fun w => hZ ((hf.ker _).mp ?_)
  rw [hf.map_mul_inv, ← hTf, hc, hc1, one_smul, sub_self]

end Lin

variable {G : Type} [Group G]

theorem conjV_commute {L V : Subgroup G} {x : G} (hxV : x ∈ Subgroup.normalizer (V : Set G))
    (hx : ∀ l ∈ L, x * l * x⁻¹ * l⁻¹ ∈ Subgroup.centralizer (V : Set G)) :
    ∀ h ∈ autOn L V, SecA.conjV V x hxV * h = h * SecA.conjV V x hxV := by
  intro h hh
  obtain ⟨l, hl, hlV, rfl⟩ := SecA.mem_autOn_iff.mp hh
  ext v
  simp only [MulAut.mul_apply, SecA.conjV_apply_coe]
  have h1 := Subgroup.mem_centralizer_iff.mp (hx l hl) (v : G) v.2
  calc x * (l * (v : G) * l⁻¹) * x⁻¹
      = (x * l * x⁻¹ * l⁻¹) * (l * (x * (v : G) * x⁻¹) * l⁻¹) * (x * l * x⁻¹ * l⁻¹)⁻¹ := by
        group
    _ = l * (x * (v : G) * x⁻¹) * l⁻¹ := by
        have h2 := Subgroup.mem_centralizer_iff.mp (hx l hl) (l * (x * (v : G) * x⁻¹) * l⁻¹)
          (by
            have h3 := (Subgroup.mem_normalizer_iff.mp hxV v).mp v.2
            exact (Subgroup.mem_normalizer_iff.mp (hlV) _).mp h3)
        rw [← h2]
        group

end BK2

theorem factCentralizerTwo_holds : FactCentralizerTwo := by
  intro G _ _ L V n hV hn hLV hVL hnat x hxV hxL hx2 hx
  obtain ⟨_, hnat⟩ := hnat
  obtain ⟨k, hk⟩ := hx2
  have hW : commV (autOn L V) = ⊤ := by
    rw [Ch10.SecA.commV_autOn_eq hLV, hVL, Subgroup.subgroupOf_self]
  have hZ : (Subgroup.centralizer (L : Set G)).subgroupOf V ≤ fixV (autOn L V) :=
    fun z hz h hh => SecA.autOn_fixes_cV h hh z hz
  have hτZ : ∀ z ∈ (Subgroup.centralizer (L : Set G)).subgroupOf V,
      SecA.conjV V x hxV z ∈ (Subgroup.centralizer (L : Set G)).subgroupOf V :=
    fun z hz => G2Q8.conjV_mem_centralizer hxL hxV hz
  have hτH := BK2.conjV_commute hxV hx
  have hτ2 := SecA.conjV_pow_eq_one V hxV hk
  have key : SecA.conjV V x hxV = 1 := by
    rcases hnat with ⟨K, _, _, hK, π, hπ⟩ | ⟨K, _, _, hK, π, hπ⟩ | ⟨K, _, _, hK, π, hπ⟩
    · have : CharP K 2 := KGNat.charP_two_of_card (by omega) hK
      obtain ⟨f, hf⟩ := KGNat.exists_isCoord (KGNat.linModelNat _) hπ
      exact BK2.eq_one_of_commute_two hf
        (fun T hT => KGNat.commutant_statedSL (by norm_num) T hT)
        (x₀ := (![1, 0, 0] : Fin 3 → K)) (fun h => one_ne_zero (congrFun h 0)) hW hZ hτZ hτH
        hτ2
    · have : CharP K 2 := KGNat.charP_two_of_card (by omega) hK
      obtain ⟨f, hf⟩ := KGNat.exists_isCoord (KGNat.linModelNat _) hπ
      exact BK2.eq_one_of_commute_two hf (fun T hT => KGNat.commutant_statedSp T hT)
        (x₀ := KGNat.vec4 (1 : K) 0 0 0) (fun h => one_ne_zero (congrFun h (.inl 0))) hW hZ hτZ
        hτH hτ2
    · have : CharP K 2 := KGNat.charP_two_of_card (by omega) hK
      obtain ⟨c₀, hc0, hc1⟩ := G2Q8.exists_ne_zero_ne_one_of_card hn hK
      obtain ⟨f, hf⟩ := KGNat.exists_isCoord (G2Q8.lmG K) hπ
      exact BK2.eq_one_of_commute_two hf
        (fun T hT => G2Q8.commutant_g2Derived hc0 hc1 G2Q8.g2Derived_le T hT)
        (x₀ := q6 (1 : K) 0 0 0 0 0) (fun h => one_ne_zero (congrFun h (.inl 0))) hW hZ hτZ
        hτH hτ2
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  have h1 := congrArg (fun τ : MulAut ↥V => ((τ ⟨v, hv⟩ : ↥V) : G)) key
  simp only [SecA.conjV_apply_coe, MulAut.one_apply] at h1
  calc v * x = x * v * x⁻¹ * x := by rw [h1]
    _ = x * v := by group

end CFSG.Quasithin.Vol2.Ch11.SecB
