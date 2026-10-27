module

public import CFSG.Quasithin.EmptyFaithful.SBc13B2Core
public import CFSG.Quasithin.EmptyFaithful.SBc13Pair
public import CFSG.Quasithin.EmptyFaithful.SBc13Mod
public import CFSG.Quasithin.EmptyFaithful.SBc13Stab
public import CFSG.Quasithin.EmptyFaithful.S146P12

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open scoped commutatorElement

namespace SBc13

variable {G : Type} [Group G] [Finite G] {T M H : Subgroup G} {p : ℕ} {H₀ H₁ H₂ K₁ K₂ : Subgroup G}
  {t s : G}

theorem pCoreOf_mcOf_fixes_U_mod_Z (S : Setting146 G T M) {H : Subgroup G} (hH : IsHTM T M H) :
    ∀ q ∈ pCoreOf 2 (mcOf T), ∀ u ∈ conjClosure (VZ T M) H,
      q * u * q⁻¹ * u⁻¹ ∈ quasithinOmegaOneCenter T := by
  intro q hq u hu
  have hHG : H ≤ mcOf T := S.le_mcOf hH
  have hTsyl : IsSylowTwoOf T (mcOf T) :=
    isSylowTwoOf_of_quasithinIsSylowTwo S.hyp.sylow S.isHTM_mcOf.1.1
  have hQT : pCoreOf 2 (mcOf T) ≤ T := isSylowTwoOf_pCoreOf_le hTsyl
  have hUab : IsElemAbelian 2 (conjClosure (VZ T M) H) := S.lemma_14_5_15_two hH
  have hcom : ∀ a, a ∈ conjClosure (VZ T M) H → ∀ b, b ∈ conjClosure (VZ T M) H →
      a * b = b * a :=
    fun a ha b hb => isElemAbelian_comm hUab ha hb
  have hZU : quasithinOmegaOneCenter T ≤ conjClosure (VZ T M) H :=
    (le_conjClosure _ _).trans (le_conjClosure _ _)
  have hHZ : ∀ h ∈ H, ∀ z ∈ quasithinOmegaOneCenter T, h * z * h⁻¹ = z := by
    intro h hh z hz
    have := S146T.comm_Z (hHG hh) hz
    rw [this]
    group
  have hTV := T_fixes_V_mod_Z_P8 S
  have hQn : ∀ h ∈ H, ∀ q ∈ pCoreOf 2 (mcOf T), h * q * h⁻¹ ∈ pCoreOf 2 (mcOf T) :=
    fun h hh q hq =>
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 (mcOf T) (hHG hh)) q).mp hq
  have key : (∀ b ∈ quasithinOmegaOneCenter T, b * u = u * b) ∧
      q * u * q⁻¹ * u⁻¹ ∈ quasithinOmegaOneCenter T := by
    induction hu using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨h, hh, y, hy, rfl⟩ := hx
      have hxU : h * y * h⁻¹ ∈ conjClosure (VZ T M) H := mem_conjClosure hh hy
      refine ⟨fun b hb => hcom b (hZU hb) _ hxU, ?_⟩
      have hq' : h⁻¹ * q * h⁻¹⁻¹ ∈ pCoreOf 2 (mcOf T) := hQn h⁻¹ (H.inv_mem hh) q hq
      have h1 := hTV _ (hQT hq') y hy
      have e : q * (h * y * h⁻¹) * q⁻¹ * (h * y * h⁻¹)⁻¹ =
          h * ((h⁻¹ * q * h⁻¹⁻¹) * y * (h⁻¹ * q * h⁻¹⁻¹)⁻¹ * y⁻¹) * h⁻¹ := by group
      rw [e, hHZ h hh _ h1]
      exact h1
    | one => exact ⟨fun b _ => by simp, by simp⟩
    | mul x y _ _ ihx ihy =>
      refine ⟨fun b hb => ?_, comm_mul_mem_P6 ihx.1 ihx.2 ihy.2⟩
      calc b * (x * y) = (b * x) * y := by group
        _ = (x * b) * y := by rw [ihx.1 b hb]
        _ = x * (b * y) := by group
        _ = x * (y * b) := by rw [ihy.1 b hb]
        _ = (x * y) * b := by group
    | inv x _ ih =>
      have hc : ∀ b ∈ quasithinOmegaOneCenter T, b * x⁻¹ = x⁻¹ * b := fun b hb => by
        have := ih.1 b hb
        calc b * x⁻¹ = x⁻¹ * (x * b) * x⁻¹ := by group
          _ = x⁻¹ * (b * x) * x⁻¹ := by rw [this]
          _ = x⁻¹ * b := by group
      refine ⟨hc, comm_left_mem_P6 (x := x⁻¹) (y := x) hc ?_ ih.2⟩
      simp
  exact key.2

theorem core_shapeOne (S : Setting146 G T M) {PQ : Subgroup G} (hred : IsRedCE T M H PQ p)
    (hdec : IsDecP T M H p H₀ H₁ H₂ t) (hset : Setup14615 T M H H₁ H₂ K₁ K₂ s)
    (hc₁ : K₁ ∈ cComp (mcOf T)) (hc₂ : K₂ ∈ cComp (mcOf T))
    (hs₁ : IsSimpleGroup (OTwoQuot K₁)) {K' : Subgroup G} (hK'le : K' ≤ K₁ ⊔ K₂)
    (hK'perf : oTwoUpper K' = K') (hs' : IsSimpleGroup (OTwoQuot K'))
    (hcard : Nat.card (OTwoQuot K') = Nat.card (OTwoQuot K₁)) {z' : G}
    (hz'U : z' ∈ uHi T M H H₁) (hz'Z : z' ∉ quasithinOmegaOneCenter T)
    (hcent : ∀ k ∈ K', k * z' = z' * k) : K' ≤ K₂ := by
  have hH : IsHTM T M H := hred.isHTM
  have hH₁H : H₁ ≤ H := hdec.le₁.trans hdec.le
  have hAG : K₁ ⊔ K₂ ≤ mcOf T := hset.kz ▸ kz_le_mcOf S hred
  have hn₂ : K₁ ⊔ K₂ ≤ Subgroup.normalizer (K₂ : Set G) := by
    obtain ⟨hle, hn⟩ := cComp_normal_span_of_le hc₂
    exact (sup_le (le_cCompSpan hc₁) hle).trans
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hle).mp hn)
  have hn₁ : K₁ ⊔ K₂ ≤ Subgroup.normalizer (K₁ : Set G) := by
    obtain ⟨hle, hn⟩ := cComp_normal_span_of_le hc₁
    exact (sup_le hle (le_cCompSpan hc₂)).trans
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hle).mp hn)
  have hGN : mcOf T ≤ Subgroup.normalizer ((K₁ ⊔ K₂ : Subgroup G) : Set G) := by
    rw [← hset.kz]
    exact le_normalizer_conjClosure _ _
  have hK₂S : ∀ k ∈ K₂, k ∈ zStab T z' := by
    intro k hk
    refine ⟨hset.le_mcOf S hred hk, ?_⟩
    have h1 : ⁅z', k⁆ ∈ quasithinOmegaOneCenter T :=
      hset.cent (Subgroup.commutator_mem_commutator hz'U hk)
    have h2 := (quasithinOmegaOneCenter T).inv_mem h1
    rw [commutatorElement_inv, commutatorElement_def] at h2
    exact h2
  have hRS : pCoreOf 2 (K₁ ⊔ K₂) ≤ zStab T z' := by
    intro r hr
    have hrQ : r ∈ pCoreOf 2 (mcOf T) :=
      le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 _).trans hAG)
        (hGN.trans (normalizer_le_normalizer_pCoreOf 2 _)) (pCoreOf_isPGroup 2 _) hr
    exact ⟨hAG (pCoreOf_le 2 _ hr),
      pCoreOf_mcOf_fixes_U_mod_Z S hH r hrQ z' (uHi_le_conjClosure hH₁H hz'U)⟩
  have hK₁C : ¬ K₁ ≤ zStab T z' ⊓ (K₁ ⊔ K₂) := by
    intro h
    obtain ⟨x, hx, hxc⟩ := exists_comm_notin_of_isDecP S hred hdec hz'U hz'Z
    exact hxc (mem_zStab.mp (h (hset.oTwo₁ hx)).1).2
  exact le_of_perfect_of_proper_stab (A := K₁ ⊔ K₂) (C := zStab T z' ⊓ (K₁ ⊔ K₂)) le_sup_left
    hK'le le_rfl hn₁ hn₂ inf_le_right (le_inf hK₂S le_sup_right) (le_inf hRS (pCoreOf_le 2 _))
    (le_inf (fun k hk => mem_zStab_of_commute (hAG (hK'le hk)) (hcent k hk)) hK'le) hK₁C hs₁
    hs' hcard hK'perf

theorem g_mem_g2_of_theta_shapeOne (S : Setting146 G T M) {PQ : Subgroup G} (_hp5 : p = 5)
    (hred : IsRedCE T M H PQ p) (hdec : IsDecP T M H p H₀ H₁ H₂ t)
    (hset : Setup14615 T M H H₁ H₂ K₁ K₂ s)
    (hc₁ : K₁ ∈ cComp (mcOf T)) (hc₂ : K₂ ∈ cComp (mcOf T))
    (_hG : mcOf T = conjClosure (oTwoUpper H) (mcOf T) ⊔ T)
    (hQ : Nonempty (OTwoQuot K₁ ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 4)))
    (hθ : Gap3Theta T K₁ K₂)
    {γ γ' : F8.Geom T (yOfL22 T M) H} {g : ↥(((yOfL22 T M) ⊔ T) ⊔ H)}
    (hF8 : F8Setup T (VZ T M) (yOfL22 T M) H γ γ' g)
    (hZ : quasithinOmegaOneCenter T ≤ conjSub (g : G) (uHi T M H H₁))
    (hcent : K₂ ≤ Subgroup.centralizer
      (F8.A₁ (quasithinOmegaOneCenter T) (g : G) : Set G)) :
    (g : G) ∈ g2_14615 K₂ := by
  have hH : IsHTM T M H := hred.isHTM
  have hQ₂ : Nonempty (OTwoQuot K₂ ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 4)) := by
    rw [hset.conj]
    exact nonempty_oTwoQuot_equiv_conjSub s hQ
  have hQ' : Nonempty (OTwoQuot (conjSub (g : G)⁻¹ K₂) ≃*
      Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 4)) :=
    nonempty_oTwoQuot_equiv_conjSub _ hQ₂
  obtain ⟨φ₁⟩ := hQ
  obtain ⟨φ'⟩ := hQ'
  obtain ⟨hsimple, -⟩ := sl2_gf16_simple_and_five_dvd
  have hs₁ : IsSimpleGroup (OTwoQuot K₁) := φ₁.isSimpleGroup
  have hs' : IsSimpleGroup (OTwoQuot (conjSub (g : G)⁻¹ K₂)) := φ'.isSimpleGroup
  have hcard : Nat.card (OTwoQuot (conjSub (g : G)⁻¹ K₂)) = Nat.card (OTwoQuot K₁) :=
    (Nat.card_congr φ'.toEquiv).trans (Nat.card_congr φ₁.toEquiv).symm
  have hgen : K₂ ≤ conjSub (g : G) (K₁ ⊔ K₂) := by
    refine (le_closure_five_of_sl2_component le_rfl hc₂ hQ₂).trans
      ((Subgroup.closure_le _).mpr fun y hy => ?_)
    obtain ⟨hyK₂, h5⟩ := hy
    have hyC : y ∈ Subgroup.centralizer
        (F8.A₁ (quasithinOmegaOneCenter T) (g : G) : Set G) := hcent hyK₂
    have hgyG : (g : G)⁻¹ * y * (g : G) ∈ mcOf T := by
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      have hzA : (g : G) * z * (g : G)⁻¹ ∈ F8.A₁ (quasithinOmegaOneCenter T) (g : G) :=
        mem_conjSub.mpr (by simpa [mul_assoc] using hz)
      have h1 := Subgroup.mem_centralizer_iff.mp hyC _ hzA
      have e : z * ((g : G)⁻¹ * y * (g : G)) = (g : G)⁻¹ * (((g : G) * z * (g : G)⁻¹) * y) *
          (g : G) := by group
      have e' : ((g : G)⁻¹ * y * (g : G)) * z = (g : G)⁻¹ * (y * ((g : G) * z * (g : G)⁻¹)) *
          (g : G) := by group
      rw [e, e', h1]
    have hord' : orderOf ((g : G)⁻¹ * y * (g : G)) = 5 := by
      rw [← h5]
      have := orderOf_injective (MulAut.conj (g : G)⁻¹).toMonoidHom
        (MulAut.conj (g : G)⁻¹).injective y
      simpa [MulAut.conj_apply, mul_assoc] using this
    exact mem_conjSub.mpr (hθ _ hgyG hord')
  have hK'le : conjSub (g : G)⁻¹ K₂ ≤ K₁ ⊔ K₂ := by
    intro k' hk'
    have h1 : (g : G) * k' * (g : G)⁻¹ ∈ K₂ := by
      have := mem_conjSub.mp hk'
      simpa using this
    have h2 := mem_conjSub.mp (hgen h1)
    simpa [mul_assoc] using h2
  have hK'perf : oTwoUpper (conjSub (g : G)⁻¹ K₂) = conjSub (g : G)⁻¹ K₂ := by
    rw [oTwoUpper_conjSub_P, hset.perf₂]
  obtain ⟨z, hz, hz1⟩ := S.exists_ne_one_Z
  have hz'U : (g : G)⁻¹ * z * (g : G) ∈ uHi T M H H₁ := mem_conjSub.mp (hZ hz)
  have hz'Z : (g : G)⁻¹ * z * (g : G) ∉ quasithinOmegaOneCenter T := by
    intro hz'
    have hz'1 : (g : G)⁻¹ * z * (g : G) ≠ 1 := by
      intro h
      apply hz1
      calc z = (g : G) * ((g : G)⁻¹ * z * (g : G)) * (g : G)⁻¹ := by group
        _ = 1 := by rw [h]; group
    apply S.conj_not_mem_Z hH hF8 hz' hz'1
    have e : (g : G) * ((g : G)⁻¹ * z * (g : G)) * (g : G)⁻¹ = z := by group
    rw [e]
    exact hz
  have hcent' : ∀ k ∈ conjSub (g : G)⁻¹ K₂,
      k * ((g : G)⁻¹ * z * (g : G)) = ((g : G)⁻¹ * z * (g : G)) * k := by
    intro k hk
    have h1 : (g : G) * k * (g : G)⁻¹ ∈ K₂ := by
      have := mem_conjSub.mp hk
      simpa using this
    have h2 := S146T.comm_Z (hset.le_mcOf S hred h1) hz
    calc k * ((g : G)⁻¹ * z * (g : G)) = (g : G)⁻¹ * (((g : G) * k * (g : G)⁻¹) * z) * (g : G) := by
          group
      _ = (g : G)⁻¹ * (z * ((g : G) * k * (g : G)⁻¹)) * (g : G) := by rw [h2]
      _ = ((g : G)⁻¹ * z * (g : G)) * k := by group
  have hle := core_shapeOne S hred hdec hset hc₁ hc₂ hs₁ hK'le hK'perf hs' hcard hz'U hz'Z hcent'
  have heq : conjSub (g : G)⁻¹ K₂ = K₂ := by
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [card_conjSub']
  have := CosetGeom.mem_normalizer_of_conjSub_eq heq
  exact (Subgroup.inv_mem_iff _).mp this

end SBc13

end CFSG.Quasithin
