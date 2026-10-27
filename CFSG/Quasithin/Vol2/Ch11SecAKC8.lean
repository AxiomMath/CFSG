module

public import CFSG.Quasithin.Vol2.Ch11SecAKC7
public import CFSG.Quasithin.Vol2.Ch11G2Q8AutV
public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesBasic

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall
  CFSG.Quasithin.Vol2.KGNat CFSG.ClassicalInvolution.ModelFacts.OddCover
  CFSG.QuasithinUnique.Bridge.Alt57Model Matrix
open CFSG.Quasithin.Vol2.Ch11.G2Q8

namespace KC8

variable {K : Type} [Field K] [CharP K 2]

theorem mem_U0_of_fix {δ : ↥(cayleyGroup K)} (hδ : ∀ y ∈ stdF K 2, g2Act δ y = y) :
    δ ∈ U0 K := by
  have hu : δ ∈ stabV0 K := by
    rw [mem_stabV0, eu_eq_q6]
    exact hδ _ (KC7.q6_mem_two _ _)
  obtain ⟨α, β, γ, A, hA, rfl⟩ := exists_eq_of_mem_stabV0 hu
  have h2 := hδ _ (KC7.q6_mem_two 0 1)
  rw [act_v2_decomp α β γ hA] at h2
  obtain ⟨e0, -, -, -, e4, e5⟩ := q6_inj h2
  obtain ⟨a0, a1, a2⟩ := adj_col0 hA
  have hdet := det_block_of_fix hA
  rw [e5, e4] at hdet
  have hA22 : (A : Matrix (Fin 3) (Fin 3) K) 2 2 = 1 := by linear_combination hdet
  rw [e5, e4] at e0
  have hβ : β = 0 := by linear_combination e0
  subst hβ
  have hAu : A = uSL ((A : Matrix (Fin 3) (Fin 3) K) 0 1) ((A : Matrix (Fin 3) (Fin 3) K) 0 2)
      ((A : Matrix (Fin 3) (Fin 3) K) 1 2) := by
    apply Subtype.ext
    have hU : ((uSL ((A : Matrix (Fin 3) (Fin 3) K) 0 1) ((A : Matrix (Fin 3) (Fin 3) K) 0 2)
        ((A : Matrix (Fin 3) (Fin 3) K) 1 2) : SL3 K) : Matrix (Fin 3) (Fin 3) K) =
        !![1, (A : Matrix (Fin 3) (Fin 3) K) 0 1, (A : Matrix (Fin 3) (Fin 3) K) 0 2;
          0, 1, (A : Matrix (Fin 3) (Fin 3) K) 1 2; 0, 0, 1] := rfl
    rw [hU]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [a0, a1, a2, e4, e5, hA22]
  rw [hAu]
  exact (U0 K).mul_mem ((U0 K).mul_mem (g2X_mem_U0 α) (g2Y_mem_U0 0 γ)) (g2A_mem_U0 _ _ _)

section Real

variable {W : Type*} [CommGroup W] {H : Subgroup (MulAut W)} {Z : Subgroup W}
  {π : ↥⁅quasithinG2 K, quasithinG2 K⁆ →* ↥H} {f : W → (Ix3 → K)}

theorem perfCentFacts [Finite K] [Finite (MulAut W)] (hW : ∀ w : W, w ^ 2 = 1)
    (hf : IsCoord (lmG K) H Z π f) {c₀ : K} (hc0 : c₀ ≠ 0) (hc1 : c₀ ≠ 1) {n : ℕ}
    (hK : Nat.card K = 2 ^ n) (hn : 2 ≤ n) (hZ : ∀ h ∈ H, ∀ z ∈ Z, h z = z)
    (hcomm : commV H = ⊤) {P : Subgroup (MulAut W)} (hP : IsPGroup 2 ↥P) {g : ↥(cayleyGroup K)}
    (hg : ∀ x : MulAut W,
      x ∈ P ↔ ∃ u ∈ U0 K, x = ((rhoG hc0 hc1 π (g * u * g⁻¹) : ↥H) : MulAut W)) :
    PerfCentFacts H Z (hf.pre (gmapG g (stdF K 2)).toAddSubgroup) := by
  have h4 := four_le_card hn hK
  set U₂ := hf.pre (gmapG g (stdF K 2)).toAddSubgroup with hU₂
  set V := commS (perfectCore (H ⊓ stabW U₂)) U₂ with hVdef
  obtain ⟨ha, -, -, -, he⟩ := KC7.lineFacts hW hf hc0 hc1 h4 hZ g
  have hV : V = (commHom (psiG hc0 hc1 π g (tL 1))).range := by
    have h := gammaW_two_eqG hf hc0 hc1 g
    change perfectCore (H ⊓ stabW U₂) = _ at h
    rw [hVdef, h]
    exact commS_eq_vt hf hc0 hc1 g hW hZ
  intro L hLp hLN hLZ hLU hLc
  have hcS : ∀ k ∈ L, ∀ s ∈ perfectCore (H ⊓ stabW U₂), ∀ u ∈ U₂, k (s u) = s (k u) := by
    intro k hk s hs u hu
    have hku : k u ∈ U₂ := (mem_stabW.mp (hLU hk) u).mp hu
    have hsku : s (k u) ∈ U₂ := (mem_stabW.mp (perfectCore_le _ hs).2 _).mp hku
    have h1 := ha _ (hLc k hk s hs) _ hsku
    simp only [MulAut.mul_apply, MulAut.inv_apply_self] at h1
    exact h1
  have hLV : ∀ k ∈ L, ∀ y ∈ V, k y ∈ V := by
    intro k hk y hy
    induction hy using Subgroup.closure_induction with
    | mem y hy =>
      obtain ⟨s, hs, u, hu, rfl⟩ := hy
      rw [map_mul, map_inv, hcS k hk s hs u hu]
      exact Subgroup.subset_closure ⟨s, hs, k u, (mem_stabW.mp (hLU hk) u).mp hu, rfl⟩
    | one => rw [map_one]; exact Subgroup.one_mem _
    | mul a b _ _ ha hb => rw [map_mul]; exact Subgroup.mul_mem _ ha hb
    | inv a _ ha => rw [map_inv]; exact Subgroup.inv_mem _ ha
  let CV : Subgroup (MulAut W) :=
    { carrier := {τ | ∀ y ∈ V, τ y = y}
      mul_mem' := fun {a b} ha hb y hy => by rw [MulAut.mul_apply, hb y hy, ha y hy]
      one_mem' := fun _ _ => rfl
      inv_mem' := fun {a} ha y hy => by
        conv_lhs => rw [← ha y hy]
        exact MulAut.inv_apply_self W a y }
  have hLCV : L ≤ CV := by
    rw [← hLp, Subgroup.commutator_le]
    intro k₁ hk₁ k₂ hk₂ y hy
    have hy' : k₁⁻¹ (k₂⁻¹ y) ∈ V := hLV _ (L.inv_mem hk₁) _ (hLV _ (L.inv_mem hk₂) _ hy)
    have h := he k₁ k₂ (fun u hu => (mem_stabW.mp (hLU hk₁) u).mp hu)
      (fun u hu => (mem_stabW.mp (hLU hk₂) u).mp hu) (fun u _ v _ => map_mul k₁ u v)
      (fun u _ v _ => map_mul k₂ u v) (hcS k₁ hk₁) (hcS k₂ hk₂) _ hy'
    simp only [MulAut.apply_inv_self] at h
    change (k₁ * k₂ * k₁⁻¹ * k₂⁻¹) y = y
    simp only [MulAut.mul_apply]
    exact h
  have hfV : ∀ x ∈ gmapG g (stdF K 2), ∃ v ∈ V, f v = x := by
    intro x hx
    obtain ⟨u, rfl⟩ := hf.surj x
    have hu : u ∈ U₂ := hx
    obtain ⟨v, hv, hvz⟩ := exists_vt hf hc0 hc1 g one_ne_zero hu
    refine ⟨v, ?_, ((hf.eq_iff u v).mpr hvz).symm⟩
    rw [hV]
    exact hv
  have hstr : ∀ k ∈ L, ∃ (c : K) (γ : ↥(cayleyGroup K)), c ≠ 0 ∧
      ∀ w, f (k w) = c • g2Act γ (f w) := by
    intro k hk
    have hkZ : ∀ z ∈ Z, k z ∈ Z := fun z hz => (mem_stabW.mp (hLZ hk) z).mp hz
    have hkZ' : ∀ z ∈ Z, k⁻¹ z ∈ Z := fun z hz => (mem_stabW.mp (hLZ (L.inv_mem hk)) z).mp hz
    have hkH' : ∀ h ∈ H, k⁻¹ * h * k ∈ H := fun h hh => by
      simpa using hLN _ (L.inv_mem hk) h hh
    obtain ⟨c, γ, σ, hc, hkf⟩ :=
      exists_smul_frob_of_normalizes hf hc0 hc1 hK hn k hkZ hkZ' (hLN k hk) hkH'
    have hσx : ∀ x ∈ gmapG g (stdF K 2), c • g2Act γ (frobQ (σ : K →+* K) x) = x := by
      intro x hx
      obtain ⟨v, hv, rfl⟩ := hfV x hx
      rw [← hkf, hLCV hk v hv]
    have hx₀ : g2Act g (eu 0 (1 : K)) ∈ gmapG g (stdF K 2) := by
      rw [mem_gmapG, g2Act_inv_apply, eu_eq_q6]
      exact KC7.q6_mem_two _ _
    have hσ : ∀ a : K, σ a = a := by
      intro a
      have h1 := hσx _ ((gmapG g (stdF K 2)).smul_mem a hx₀)
      rw [frobQ_smul, G2Q8.g2Act_smul, smul_comm, hσx _ hx₀] at h1
      exact smul_left_injective K (g2Act_eu_ne_zero g) h1
    have hfrob : ∀ x, frobQ (σ : K →+* K) x = x := fun x => by
      funext j
      exact hσ (x j)
    exact ⟨c, γ, hc, fun w => by rw [hkf, hfrob]⟩
  let M : Subgroup (MulAut W) :=
    { carrier := {τ | ∃ γ : ↥(cayleyGroup K), ∀ w, f (τ w) = g2Act γ (f w)}
      mul_mem' := by
        rintro a b ⟨γa, ha⟩ ⟨γb, hb⟩
        exact ⟨γa * γb, fun w => by rw [MulAut.mul_apply, ha, hb, g2Act_mul_apply]⟩
      one_mem' := ⟨1, fun w => by rw [map_one]; rfl⟩
      inv_mem' := by
        rintro a ⟨γ, ha⟩
        refine ⟨γ⁻¹, fun w => ?_⟩
        rw [show f w = g2Act γ (f (a⁻¹ w)) by rw [← ha, MulAut.apply_inv_self],
          g2Act_inv_apply] }
  have hLM : L ≤ M := by
    rw [← hLp, Subgroup.commutator_le]
    intro k₁ hk₁ k₂ hk₂
    obtain ⟨c₁, γ₁, hc₁, h₁⟩ := hstr k₁ hk₁
    obtain ⟨c₂, γ₂, hc₂, h₂⟩ := hstr k₂ hk₂
    have hinv : ∀ {k : MulAut W} {c : K} {γ : ↥(cayleyGroup K)}, c ≠ 0 →
        (∀ w, f (k w) = c • g2Act γ (f w)) → ∀ w, f (k⁻¹ w) = c⁻¹ • g2Act γ⁻¹ (f w) := by
      intro k c γ hc h w
      rw [show f w = c • g2Act γ (f (k⁻¹ w)) by rw [← h, MulAut.apply_inv_self],
        G2Q8.g2Act_smul, g2Act_inv_apply, smul_smul, inv_mul_cancel₀ hc, one_smul]
    refine ⟨γ₁ * γ₂ * γ₁⁻¹ * γ₂⁻¹, fun w => ?_⟩
    change f ((k₁ * k₂ * k₁⁻¹ * k₂⁻¹) w) = _
    simp only [MulAut.mul_apply]
    rw [h₁, h₂, hinv hc₁ h₁, hinv hc₂ h₂]
    simp only [G2Q8.g2Act_smul, smul_smul, g2Act_mul_apply]
    rw [show c₁ * (c₂ * (c₁⁻¹ * c₂⁻¹)) = 1 by field_simp, one_smul]
  have hLP : L ≤ P := by
    intro k hk
    obtain ⟨γ, hγ⟩ := hLM hk
    have hγF : ∀ x ∈ gmapG g (stdF K 2), g2Act γ x = x := by
      intro x hx
      obtain ⟨v, hv, rfl⟩ := hfV x hx
      rw [← hγ, hLCV hk v hv]
    have hkρ : k = ((rhoG hc0 hc1 π γ : ↥H) : MulAut W) :=
      eq_rhoG_of_modZ hf hc0 hc1 hcomm (fun z hz h hh => hZ h hh z hz) (hLN k hk) hγ
    have hδ : g⁻¹ * γ * g ∈ U0 K := by
      refine KC8.mem_U0_of_fix fun y hy => ?_
      have hgy : g2Act g y ∈ gmapG g (stdF K 2) := by
        rw [mem_gmapG, g2Act_inv_apply]
        exact hy
      rw [g2Act_mul_apply, g2Act_mul_apply, hγF _ hgy, g2Act_inv_apply]
    exact (hg k).mpr ⟨_, hδ, by rw [hkρ, show g * (g⁻¹ * γ * g) * g⁻¹ = γ by group]⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hbot : L = ⊥ := by
    have : Group.IsNilpotent ↥L := (hP.to_le hLP).isNilpotent
    have : Group.IsPerfect ↥L := Subgroup.isPerfect_iff.mpr hLp
    by_contra hne
    have : Nontrivial ↥L := (Subgroup.nontrivial_iff_ne_bot _).mpr hne
    exact Group.IsPerfect.not_isSolvable (G := ↥L) inferInstance
  intro k hk w
  rw [hbot, Subgroup.mem_bot] at hk
  rw [hk]
  rfl

end Real

end KC8

open KC7 KC8 in
theorem factLineG2_holds : FactLineG2 := by
  intro K _ _ n hn hK W _ _ hW H Z π hπ hZ P hP U₂ hU₂
  have : CharP K 2 := KGNat.charP_two_of_card (by omega) hK
  have : Finite (MulAut W) := Finite.of_injective _ MulEquiv.toEquiv_injective
  have h4 := four_le_card hn hK
  obtain ⟨c₀, hc0, hc1⟩ := exists_ne_zero_ne_one_of_card hn hK
  obtain ⟨f, hf⟩ := exists_isCoord (lmG K) hπ
  obtain ⟨g, hg⟩ := exists_sylow_eq_conj_U0 hK (by omega) hf hc0 hc1 hP
  have hU := eq_U2_of_isFlagWG hW hf hc0 hc1 hg (by rw [hK]; exact hU₂)
  subst hU
  exact ⟨lineFacts hW hf hc0 hc1 h4 hZ g,
    fun hcomm => perfCentFacts hW hf hc0 hc1 hK hn hZ hcomm hP.isPGroup hg⟩

end CFSG.Quasithin.Vol2.Ch11.SecA
