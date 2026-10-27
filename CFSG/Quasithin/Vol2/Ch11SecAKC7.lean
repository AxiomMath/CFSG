module

public import CFSG.Quasithin.Vol2.Ch11G2Q8RadLift
public import CFSG.Quasithin.Vol2.KGNatSL3LineFacts
public import CFSG.Quasithin.Background.C118NoOuterAlg

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall
  CFSG.Quasithin.Vol2.KGNat Matrix
open CFSG.Quasithin.Vol2.Ch11.G2Q8
open CFSG.Quasithin.Vol2.Ch11.SecS.C11P9A (pCoreOf_map_of_injective)

namespace KC7

variable {K : Type} [Field K]

theorem eq_of_upart_eq {y y' : Ix3 → K} (hy : y ∈ stdF K 2) (hy' : y' ∈ stdF K 2)
    (h : upart y = upart y') : y = y' := by
  obtain ⟨a1, a2, a3, a4⟩ := mem_stdF_two.mp hy
  obtain ⟨b1, b2, b3, b4⟩ := mem_stdF_two.mp hy'
  have h0 : y (.inl 0) = y' (.inl 0) := congrFun h 0
  have h1 : y (.inr 2) = y' (.inr 2) := congrFun h 1
  funext k
  rcases k with k | k <;> fin_cases k
  · exact h0
  · exact a1.trans b1.symm
  · exact a2.trans b2.symm
  · exact a3.trans b3.symm
  · exact a4.trans b4.symm
  · exact h1

theorem q6_mem_two (a b : K) : q6 a 0 0 0 0 b ∈ stdF K 2 := mem_stdF_two.mpr ⟨rfl, rfl, rfl, rfl⟩

theorem upart_q6 (x : Fin 2 → K) : upart (q6 (x 0) 0 0 0 0 (x 1)) = x := by
  funext i
  fin_cases i <;> rfl

variable [CharP K 2]

theorem fix_of_levi2Mat {γ : ↥(cayleyGroup K)} (hγ : γ ∈ stabQ (stdF K 2)) (h : levi2Mat γ = 1)
    {y : Ix3 → K} (hy : y ∈ stdF K 2) : g2Act γ y = y :=
  eq_of_upart_eq ((mem_stabQ.mp hγ y).mp hy) hy (by rw [upart_act γ hy, h, one_mulVec])

theorem eq_zero_of_fix {y : Ix3 → K} (hy : y ∈ stdF K 2)
    (hX : g2Act (g2X ![0, 1, 0]) y = y) (hY : g2Act (g2Y ![0, 1, 0]) y = y) : y = 0 := by
  obtain ⟨y1, y2, y3, y4⟩ := mem_stdF_two.mp hy
  rw [q6_eta y, y1, y2, y3, y4, g2Act_x1q] at hX
  rw [q6_eta y, y1, y2, y3, y4, g2Act_y12q] at hY
  obtain ⟨-, -, -, -, -, e5⟩ := q6_inj hX
  obtain ⟨e0, -, -, -, -, -⟩ := q6_inj hY
  have h0 : y (.inl 0) = 0 := by linear_combination e5
  have h5 : y (.inr 2) = 0 := by linear_combination e0
  funext k
  rcases k with k | k <;> fin_cases k
  · exact h0
  · exact y1
  · exact y2
  · exact y3
  · exact y4
  · exact h5

section Real

variable {W : Type*} [CommGroup W] {H : Subgroup (MulAut W)} {Z : Subgroup W}
  {π : ↥⁅quasithinG2 K, quasithinG2 K⁆ →* ↥H} {f : W → (Ix3 → K)}

theorem exists_scalar [Finite K] (hf : IsCoord (lmG K) H Z π f) {c₀ : K} (hc0 : c₀ ≠ 0)
    (hc1 : c₀ ≠ 1) (h4 : 4 ≤ Nat.card K) (hZ : ∀ h ∈ H, ∀ z ∈ Z, h z = z)
    (g : ↥(cayleyGroup K)) {U₂ : Subgroup W} (hU₂ : U₂ = hf.pre (gmapG g (stdF K 2)).toAddSubgroup)
    (hfix : ∀ u ∈ U₂, (∀ s ∈ perfectCore (H ⊓ stabW U₂), s u = u) → u ∈ Z) {θ : W → W}
    (hθU : ∀ u ∈ U₂, θ u ∈ U₂) (hθm : ∀ u ∈ U₂, ∀ v ∈ U₂, θ (u * v) = θ u * θ v)
    (hθS : ∀ s ∈ perfectCore (H ⊓ stabW U₂), ∀ u ∈ U₂, θ (s u) = s (θ u)) :
    ∃ c : K, ∀ u ∈ U₂, f (θ u) = c • f u := by
  subst hU₂
  set U₂ := hf.pre (gmapG g (stdF K 2)).toAddSubgroup with hU₂def
  have hZU : Z ≤ U₂ := hf.le_pre _
  have hθZ : ∀ z ∈ Z, θ z ∈ Z := fun z hz => hfix _ (hθU z (hZU hz)) fun s hs => by
    rw [← hθS s hs z (hZU hz), hZ s (perfectCore_le _ hs).1 z hz]
  have hθf : ∀ u ∈ U₂, ∀ v ∈ U₂, f u = f v → f (θ u) = f (θ v) := by
    intro u hu v hv h
    have hz : u * v⁻¹ ∈ Z := (hf.eq_iff u v).mp h
    have h1 : θ u = θ (u * v⁻¹) * θ v := by
      rw [← hθm _ (U₂.mul_mem hu (U₂.inv_mem hv)) _ hv, inv_mul_cancel_right]
    rw [h1, hf.map_mul, (hf.ker _).mpr (hθZ _ hz), zero_add]
  have hsec : ∀ x : Fin 2 → K, ∃ u ∈ U₂, g2Act g⁻¹ (f u) = q6 (x 0) 0 0 0 0 (x 1) := by
    intro x
    obtain ⟨u, hu⟩ := hf.surj (g2Act g (q6 (x 0) 0 0 0 0 (x 1)))
    have e : g2Act g⁻¹ (f u) = q6 (x 0) 0 0 0 0 (x 1) := by rw [hu, g2Act_inv_apply]
    refine ⟨u, ?_, e⟩
    change f u ∈ gmapG g (stdF K 2)
    rw [mem_gmapG, e]
    exact q6_mem_two _ _
  choose sec hsecU hsecf using hsec
  have hθF : ∀ u ∈ U₂, g2Act g⁻¹ (f (θ u)) ∈ stdF K 2 := fun u hu => mem_gmapG.mp (hθU u hu)
  have hdet : ∀ u ∈ U₂, ∀ v ∈ U₂,
      upart (g2Act g⁻¹ (f u)) = upart (g2Act g⁻¹ (f v)) → f u = f v := by
    intro u hu v hv h
    have h2 := congrArg (g2Act g) (eq_of_upart_eq (mem_gmapG.mp hu) (mem_gmapG.mp hv) h)
    rwa [g2Act_apply_inv, g2Act_apply_inv] at h2
  set T : (Fin 2 → K) → (Fin 2 → K) := fun x => upart (g2Act g⁻¹ (f (θ (sec x)))) with hT
  have hadd : ∀ x y, T (x + y) = T x + T y := by
    intro x y
    have h1 : f (sec (x + y)) = f (sec x * sec y) :=
      hdet _ (hsecU _) _ (U₂.mul_mem (hsecU x) (hsecU y)) (by
        rw [hsecf, upart_q6, hf.map_mul, map_add, hsecf, hsecf, upart_add, upart_q6, upart_q6])
    simp only [hT]
    rw [hθf _ (hsecU _) _ (U₂.mul_mem (hsecU x) (hsecU y)) h1, hθm _ (hsecU x) _ (hsecU y),
      hf.map_mul, map_add, upart_add]
  have hcomm : ∀ (A : SpecialLinearGroup (Fin 2) K) (x : Fin 2 → K),
      T ((A : Matrix (Fin 2) (Fin 2) K) *ᵥ x) = (A : Matrix (Fin 2) (Fin 2) K) *ᵥ T x := by
    intro A x
    obtain ⟨γ, hγ⟩ := levi2_surjective h4 A
    have hγS : psiG hc0 hc1 π g γ.1 ∈ perfectCore (H ⊓ stabW U₂) := by
      have h := gammaW_two_eqG hf hc0 hc1 g
      change perfectCore (H ⊓ stabW U₂) = _ at h
      rw [h]
      exact ⟨γ.1, γ.2, rfl⟩
    have hA : (A : Matrix (Fin 2) (Fin 2) K) = levi2Mat γ.1 := by rw [← hγ, levi2_apply]
    have hsU : psiG hc0 hc1 π g γ.1 (sec x) ∈ U₂ :=
      (mem_stabW.mp (perfectCore_le _ hγS).2 _).mp (hsecU x)
    have hfs : ∀ w, g2Act g⁻¹ (f (psiG hc0 hc1 π g γ.1 w)) =
        g2Act γ.1 (g2Act g⁻¹ (f w)) := fun w => by rw [f_psiG hf, g2Act_inv_apply]
    have h1 : f (sec ((A : Matrix (Fin 2) (Fin 2) K) *ᵥ x)) =
        f (psiG hc0 hc1 π g γ.1 (sec x)) := hdet _ (hsecU _) _ hsU (by
      rw [hsecf, upart_q6, hfs, hsecf, upart_act _ (q6_mem_two _ _), upart_q6, hA])
    simp only [hT]
    rw [hθf _ (hsecU _) _ hsU h1, hθS _ hγS _ (hsecU x), hfs, upart_act _ (hθF _ (hsecU x)), hA]
  obtain ⟨d, hd⟩ := commutant_sl2 T hadd hcomm
  refine ⟨d, fun u hu => ?_⟩
  have hsecu : f u = f (sec (upart (g2Act g⁻¹ (f u)))) :=
    hdet u hu _ (hsecU _) (by rw [hsecf, upart_q6])
  have h2 : g2Act g⁻¹ (f (θ u)) = d • g2Act g⁻¹ (f u) := by
    apply eq_of_upart_eq (hθF u hu) ((stdF K 2).smul_mem d (mem_gmapG.mp hu))
    rw [upart_smul, ← hd, hT, hθf _ hu _ (hsecU _) hsecu]
  have h3 := congrArg (g2Act g) h2
  rwa [g2Act_apply_inv, G2Q8.g2Act_smul, g2Act_apply_inv] at h3

theorem lineFacts [Finite K] [Finite (MulAut W)] (hW : ∀ w : W, w ^ 2 = 1)
    (hf : IsCoord (lmG K) H Z π f) {c₀ : K} (hc0 : c₀ ≠ 0) (hc1 : c₀ ≠ 1)
    (h4 : 4 ≤ Nat.card K) (hZ : ∀ h ∈ H, ∀ z ∈ Z, h z = z) (g : ↥(cayleyGroup K)) :
    LineFacts H Z (hf.pre (gmapG g (stdF K 2)).toAddSubgroup) := by
  have := finite_cayleyGroup (F := K)
  set U₂ := hf.pre (gmapG g (stdF K 2)).toAddSubgroup with hU₂
  have hψi : Function.Injective (psiG hc0 hc1 π g) := psiG_injective hf hc0 hc1 g
  have hS₂ : perfectCore (H ⊓ stabW U₂) =
      (perfectCore (stabQ (stdF K 2))).map (psiG hc0 hc1 π g) := gammaW_two_eqG hf hc0 hc1 g
  have ha : ((Units.mk0 c₀ hc0 : Kˣ) : K) ≠ 1 := hc1
  have hV : commS (perfectCore (H ⊓ stabW U₂)) U₂ =
      (commHom (psiG hc0 hc1 π g (tL 1))).range := by
    rw [hS₂]
    exact commS_eq_vt hf hc0 hc1 g hW hZ
  have hVZ : (commHom (psiG hc0 hc1 π g (tL 1))).range ⊓ Z = ⊥ :=
    vt_inf_Z hf hc0 hc1 g hW hZ one_ne_zero ha
  have hZU : Z ≤ U₂ := hf.le_pre _
  have hmemS : ∀ γ ∈ perfectCore (stabQ (stdF K 2)),
      psiG hc0 hc1 π g γ ∈ perfectCore (H ⊓ stabW U₂) := fun γ hγ => by
    rw [hS₂]
    exact ⟨γ, hγ, rfl⟩
  have hsl : ∀ k ∈ sl2E1 K, k ∈ perfectCore (stabQ (stdF K 2)) := fun k hk =>
    le_perfectCore_of_perfect sl2E1_le_stabQ (sl2E1_perfect hc0 hc1) hk
  have hX : g2X ![0, (1 : K), 0] ∈ perfectCore (stabQ (stdF K 2)) :=
    hsl _ (Subgroup.subset_closure ⟨1, Or.inl rfl⟩)
  have hY : g2Y ![0, (1 : K), 0] ∈ perfectCore (stabQ (stdF K 2)) :=
    hsl _ (Subgroup.subset_closure ⟨1, Or.inr rfl⟩)
  have hfψ : ∀ γ w, g2Act g⁻¹ (f (psiG hc0 hc1 π g γ w)) = g2Act γ (g2Act g⁻¹ (f w)) :=
    fun γ w => by rw [f_psiG hf, g2Act_inv_apply]
  have hfix : ∀ u ∈ U₂, (∀ s ∈ perfectCore (H ⊓ stabW U₂), s u = u) ↔ u ∈ Z := by
    intro u hu
    refine ⟨fun h => ?_, fun hz s hs => hZ s (perfectCore_le _ hs).1 u hz⟩
    have h1 := congrArg (fun w => g2Act g⁻¹ (f w)) (h _ (hmemS _ hX))
    have h2 := congrArg (fun w => g2Act g⁻¹ (f w)) (h _ (hmemS _ hY))
    simp only [hfψ] at h1 h2
    have h0 := eq_zero_of_fix (mem_gmapG.mp hu) h1 h2
    rw [← hf.ker, ← g2Act_apply_inv g (f u), h0, map_zero]
  refine ⟨?_, ?_, hfix, ?_, ?_⟩
  ·
    intro s hs u hu
    rw [hS₂, pCoreOf_map_of_injective _ hψi] at hs
    obtain ⟨γ, hγ, rfl⟩ := hs
    obtain ⟨hγP, hγL⟩ := (mem_pCoreOf_gam2_iff h4).mp hγ
    have hz : psiG hc0 hc1 π g γ u * u⁻¹ ∈ Z := by
      rw [← hf.eq_iff, ← g2Act_apply_inv g (f (psiG hc0 hc1 π g γ u)), hfψ,
        fix_of_levi2Mat (perfectCore_le _ hγP) hγL (mem_gmapG.mp hu), g2Act_apply_inv]
    have hv : psiG hc0 hc1 π g γ u * u⁻¹ ∈ (commHom (psiG hc0 hc1 π g (tL 1))).range := by
      rw [← hV]
      exact Subgroup.subset_closure ⟨_, hmemS γ hγP, u, hu, rfl⟩
    have h := hVZ.le ⟨hv, hz⟩
    rw [Subgroup.mem_bot, mul_inv_eq_one] at h
    exact h
  ·
    obtain ⟨u, hu⟩ := hf.surj (g2Act g (q6 1 0 0 0 0 0))
    have hu' : g2Act g⁻¹ (f u) = q6 1 0 0 0 0 0 := by rw [hu, g2Act_inv_apply]
    refine ⟨_, hmemS _ hX, u, ?_, fun h => ?_⟩
    · change f u ∈ gmapG g (stdF K 2)
      rw [mem_gmapG, hu']
      exact q6_mem_two _ _
    · have h1 := congrArg (fun w => g2Act g⁻¹ (f w)) h
      simp only [hfψ, hu', g2Act_x1q] at h1
      have h2 := congrFun h1 (.inr 2)
      simp [q6] at h2
  ·
    rw [hV]
    refine le_antisymm (fun u hu => ?_) (sup_le (vt_le_U2 hf hc0 hc1 g 1) hZU)
    obtain ⟨v, hv, hvz⟩ := exists_vt hf hc0 hc1 g one_ne_zero hu
    rw [show u = v * (u * v⁻¹) by rw [mul_comm u, mul_inv_cancel_left]]
    exact Subgroup.mul_mem_sup hv hvz
  ·
    intro φ ψ hφU hψU hφm hψm hφS hψS
    have hfix' : ∀ u ∈ U₂, (∀ s ∈ perfectCore (H ⊓ stabW U₂), s u = u) → u ∈ Z :=
      fun u hu => (hfix u hu).mp
    obtain ⟨c, hc⟩ := exists_scalar hf hc0 hc1 h4 hZ g hU₂ hfix' hφU hφm hφS
    obtain ⟨d, hd⟩ := exists_scalar hf hc0 hc1 h4 hZ g hU₂ hfix' hψU hψm hψS
    have hχZ : ∀ u ∈ U₂, φ (ψ u) * (ψ (φ u))⁻¹ ∈ Z := fun u hu => (hf.eq_iff _ _).mp (by
      rw [hc _ (hψU u hu), hd u hu, hd _ (hφU u hu), hc u hu, smul_smul, smul_smul, mul_comm])
    let C : Subgroup W :=
      { carrier := {y | y ∈ U₂ ∧ φ (ψ y) = ψ (φ y)}
        mul_mem' := fun {a b} ha hb => ⟨Subgroup.mul_mem _ ha.1 hb.1, by
          rw [hψm _ ha.1 _ hb.1, hφm _ (hψU _ ha.1) _ (hψU _ hb.1), ha.2, hb.2,
            hφm _ ha.1 _ hb.1, hψm _ (hφU _ ha.1) _ (hφU _ hb.1)]⟩
        one_mem' := ⟨Subgroup.one_mem _, by
          rw [map_one_of_mul hψm, map_one_of_mul hφm, map_one_of_mul hψm]⟩
        inv_mem' := fun {a} ha => ⟨Subgroup.inv_mem _ ha.1, by
          rw [map_inv_of_mul hψm ha.1, map_inv_of_mul hφm (hψU _ ha.1), ha.2,
            map_inv_of_mul hφm ha.1, map_inv_of_mul hψm (hφU _ ha.1)]⟩ }
    have hle : commS (perfectCore (H ⊓ stabW U₂)) U₂ ≤ C := by
      refine (Subgroup.closure_le _).mpr ?_
      rintro _ ⟨s, hs, u, hu, rfl⟩
      have hst := mem_stabW.mp (perfectCore_le _ hs).2
      have hsu := (hst u).mp hu
      have hψu := hψU u hu
      have hφu := hφU u hu
      refine ⟨Subgroup.mul_mem _ hsu (Subgroup.inv_mem _ hu), ?_⟩
      rw [hψm _ hsu _ (Subgroup.inv_mem _ hu), map_inv_of_mul hψm hu, hψS s hs u hu,
        hφm _ ((hst _).mp hψu) _ (Subgroup.inv_mem _ hψu), map_inv_of_mul hφm hψu,
        hφS s hs _ hψu, hφm _ hsu _ (Subgroup.inv_mem _ hu), map_inv_of_mul hφm hu,
        hφS s hs u hu, hψm _ ((hst _).mp hφu) _ (Subgroup.inv_mem _ hφu),
        map_inv_of_mul hψm hφu, hψS s hs _ hφu]
      obtain ⟨z, hz, hzdef⟩ : ∃ z ∈ Z, φ (ψ u) = z * ψ (φ u) := ⟨_, hχZ u hu, by group⟩
      rw [hzdef, map_mul, hZ s (perfectCore_le _ hs).1 z hz, mul_comm z, _root_.mul_inv_rev,
        mul_comm (ψ (φ u))⁻¹, mul_assoc, mul_inv_cancel_left]
    intro y hy
    exact (hle hy).2

end Real

end KC7

end CFSG.Quasithin.Vol2.Ch11.SecA
