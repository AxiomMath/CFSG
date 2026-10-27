module

public import CFSG.Quasithin.Vol2.Ch11G2Q8Real
public import CFSG.Quasithin.Vol2.KGNatPointT
public import CFSG.Quasithin.Vol2.Ch11SecAFacts11

public section

namespace CFSG.Quasithin.Vol2.Ch11.G2Q8

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall
  CFSG.Quasithin.Vol2.KGNat CFSG.ClassicalInvolution.ModelFacts.OddCover Matrix

variable {K : Type} [Field K] [CharP K 2]

theorem g2Act_smul (g : ↥(cayleyGroup K)) (t : K) (x : Ix3 → K) :
    g2Act g (t • x) = t • g2Act g x := by
  rw [← zornLin_apply_eq, map_smul, zornLin_apply_eq]

omit [CharP K 2] in
theorem mem_stdF_one_iff {x : Ix3 → K} : x ∈ stdF K 1 ↔ ∃ t : K, x = t • eu 0 1 := by
  constructor
  · intro hx
    refine ⟨x (.inl 0), funext fun k => ?_⟩
    by_cases hk : k = .inl 0
    · subst hk
      simp
    · have hk1 : 1 ≤ ht k := by
        rcases k with k | k <;> fin_cases k
        · exact absurd rfl hk
        all_goals decide
      rw [hx k hk1]
      simp [eu, Pi.single_eq_of_ne hk]
  · rintro ⟨t, rfl⟩ k hk
    have hk0 : k ≠ .inl 0 := by
      rintro rfl
      exact absurd hk (by decide)
    simp [eu, Pi.single_eq_of_ne hk0]

theorem mem_gmapG_stdF_one_iff {g : ↥(cayleyGroup K)} {x : Ix3 → K} :
    x ∈ gmapG g (stdF K 1) ↔ ∃ t : K, x = t • g2Act g (eu 0 1) := by
  rw [mem_gmapG, mem_stdF_one_iff]
  constructor
  · rintro ⟨t, ht⟩
    refine ⟨t, ?_⟩
    rw [← g2Act_smul, ← ht, g2Act_apply_inv]
  · rintro ⟨t, rfl⟩
    exact ⟨t, by rw [g2Act_smul, g2Act_inv_apply]⟩

theorem g2Act_eu_ne_zero (g : ↥(cayleyGroup K)) : g2Act g (eu 0 (1 : K)) ≠ 0 := by
  intro h
  have h1 := congrArg (g2Act g⁻¹) h
  rw [g2Act_inv_apply, map_zero] at h1
  have := congrFun h1 (.inl 0)
  simp at this

section Point

variable {W : Type*} [CommGroup W] {H : Subgroup (MulAut W)} {Z : Subgroup W}
  {π : ↥⁅quasithinG2 K, quasithinG2 K⁆ →* ↥H} {f : W → (Ix3 → K)}

theorem eq_U1_of_isFlagWG [Finite K] (hW : ∀ w : W, w ^ 2 = 1) (hf : IsCoord (lmG K) H Z π f)
    {c : K} (hc0 : c ≠ 0) (hc1 : c ≠ 1) {P : Subgroup (MulAut W)} {g : ↥(cayleyGroup K)}
    (hg : ∀ x : MulAut W,
      x ∈ P ↔ ∃ u ∈ U0 K, x = ((rhoG hc0 hc1 π (g * u * g⁻¹) : ↥H) : MulAut W))
    {U : Subgroup W} (hU : Ch11.SecA.IsFlagW H P Z (Nat.card K) 1 U) :
    U = hf.pre (gmapG g (stdF K 1)).toAddSubgroup := by
  obtain ⟨S, hS, hc, rfl⟩ := exists_eq_preG_of_isFlagW hW hf hc0 hc1 hg hU
  rw [eq_stdF_of_card hS hc]

theorem exists_scalar_of_mem_stabG (hf : IsCoord (lmG K) H Z π f) {c₀ : K} (hc0 : c₀ ≠ 0)
    (hc1 : c₀ ≠ 1) (g : ↥(cayleyGroup K)) {s : MulAut W}
    (hs : s ∈ H ⊓ Ch11.SecA.stabW (hf.pre (gmapG g (stdF K 1)).toAddSubgroup)) :
    ∃ c : Kˣ, ∀ w, f w ∈ gmapG g (stdF K 1) → f (s w) = (c : K) • f w := by
  obtain ⟨hsH, hsU⟩ := hs
  obtain ⟨A, hA⟩ := (rhoG_bijective hf hc0 hc1).2 ⟨s, hsH⟩
  have hsA : s = ((rhoG hc0 hc1 π A : ↥H) : MulAut W) := by rw [hA]
  set v₀ := g2Act g (eu 0 (1 : K)) with hv₀
  obtain ⟨w₀, hw₀⟩ := hf.surj v₀
  have h0 : f w₀ ∈ gmapG g (stdF K 1) := mem_gmapG_stdF_one_iff.mpr ⟨1, by rw [hw₀, one_smul]⟩
  have h1 : f (s w₀) ∈ gmapG g (stdF K 1) := (Ch11.SecA.mem_stabW.mp hsU w₀).mp h0
  obtain ⟨c, hc⟩ := mem_gmapG_stdF_one_iff.mp h1
  have hAv : g2Act A v₀ = c • v₀ := by
    rw [← hw₀, ← IsCoord.actG hf hc0 hc1, ← hsA, hc, hw₀]
  have hcne : c ≠ 0 := by
    intro hz
    rw [hz, zero_smul] at hAv
    have := congrArg (g2Act A⁻¹) hAv
    rw [g2Act_inv_apply, map_zero] at this
    exact g2Act_eu_ne_zero g this
  refine ⟨Units.mk0 c hcne, fun w hw => ?_⟩
  obtain ⟨t, ht⟩ := mem_gmapG_stdF_one_iff.mp hw
  rw [hsA, IsCoord.actG hf hc0 hc1, ht, g2Act_smul, hAv, Units.val_mk0, smul_smul, smul_smul,
    mul_comm]

@[expose] noncomputable def tG (c : Kˣ) : ↥(cayleyGroup K) :=
  g2A (diag3 (c : K) (c⁻¹ : Kˣ) 1 (by simp))

theorem g2Act_tG_eu (c : Kˣ) (t : K) : g2Act (tG c) (eu 0 t) = eu 0 ((c : K) * t) := by
  rw [tG, show (eu 0 t : Ix3 → K) = q6 t 0 0 0 0 0 by
    funext k; rcases k with k | k <;> fin_cases k <;> simp [q6], g2Act_diag3]
  funext k
  rcases k with k | k <;> fin_cases k <;> simp [q6]

omit [CharP K 2] in
theorem smul_eu (t s : K) : t • (eu 0 s : Ix3 → K) = eu 0 (t * s) := by
  funext k
  by_cases hk : k = .inl 0
  · subst hk
    simp [eu]
  · simp [eu, Pi.single_eq_of_ne hk]

omit [CharP K 2] in
theorem tG_mul (c d : Kˣ) : tG (c * d) = tG c * tG d := by
  rw [tG, tG, tG, ← map_mul, diag3_mul _ _ (by
    simp only [mul_one]
    rw [mul_mul_mul_comm, Units.mul_inv, Units.mul_inv, mul_one])]
  congr 1
  exact diag3_congr (by simp) (by simp [mul_comm]) (by simp)

@[expose] noncomputable def tGHom : Kˣ →* ↥(cayleyGroup K) :=
  MonoidHom.mk' tG tG_mul

omit [CharP K 2] in
theorem tG_zpow (c : Kˣ) (k : ℤ) : tG c ^ k = tG (c ^ k) :=
  (map_zpow (tGHom (K := K)) c k).symm

omit [CharP K 2] in
theorem tG_inv (c : Kˣ) : (tG c)⁻¹ = tG c⁻¹ :=
  (map_inv (tGHom (K := K)) c).symm

theorem tG_mem_stab (c : Kˣ) (x : Ix3 → K) :
    g2Act (tG c) x ∈ stdF K 1 ↔ x ∈ stdF K 1 := by
  constructor
  · intro hx
    obtain ⟨t, ht⟩ := mem_stdF_one_iff.mp hx
    refine mem_stdF_one_iff.mpr ⟨((c⁻¹ : Kˣ) : K) * t, ?_⟩
    have e : x = g2Act (tG c)⁻¹ (g2Act (tG c) x) := (g2Act_inv_apply _ x).symm
    rw [e, ht, tG_inv, g2Act_smul, g2Act_tG_eu, mul_one, smul_eu, smul_eu, mul_one, mul_comm]
  · intro hx
    obtain ⟨t, rfl⟩ := mem_stdF_one_iff.mp hx
    refine mem_stdF_one_iff.mpr ⟨(c : K) * t, ?_⟩
    rw [g2Act_smul, g2Act_tG_eu, mul_one, smul_eu, smul_eu, mul_one, mul_comm]

theorem act_diagG (hf : IsCoord (lmG K) H Z π f) {c₀ : K} (hc0 : c₀ ≠ 0) (hc1 : c₀ ≠ 1)
    (g : ↥(cayleyGroup K)) (c : Kˣ) {w : W} (hw : f w ∈ gmapG g (stdF K 1)) :
    f (((rhoG hc0 hc1 π (g * tG c * g⁻¹) : ↥H) : MulAut W) w) = (c : K) • f w := by
  obtain ⟨t, ht⟩ := mem_gmapG_stdF_one_iff.mp hw
  rw [IsCoord.actG hf hc0 hc1, ht, g2Act_smul, g2Act_mul_apply, g2Act_mul_apply, g2Act_inv_apply,
    g2Act_tG_eu, mul_one, show (eu 0 (c : K) : Ix3 → K) = (c : K) • eu 0 1 by
      rw [← Pi.single_smul, smul_eq_mul, mul_one], g2Act_smul, smul_smul, smul_smul, mul_comm]

theorem mem_stab_diagG (hf : IsCoord (lmG K) H Z π f) {c₀ : K} (hc0 : c₀ ≠ 0) (hc1 : c₀ ≠ 1)
    (g : ↥(cayleyGroup K)) (c : Kˣ) :
    ((rhoG hc0 hc1 π (g * tG c * g⁻¹) : ↥H) : MulAut W) ∈
      Ch11.SecA.stabW (hf.pre (gmapG g (stdF K 1)).toAddSubgroup) := by
  rw [IsCoord.rhoG_mem_stabW_iff hf hc0 hc1 (hf.le_pre _), hf.img_pre]
  intro y
  change y ∈ gmapG g _ ↔ _ ∈ gmapG g _
  rw [mem_gmapG, mem_gmapG, conj_g2Act, tG_mem_stab]

end Point

theorem factPointG2A_holds : Ch11.SecA.FactPointG2 := by
  intro K _ _ n hn hK W _ _ hW H Z π hπ P hP U hU
  have : CharP K 2 := charP_two_of_card (by omega) hK
  obtain ⟨c, hc0, hc1⟩ := exists_ne_zero_ne_one_of_card hn hK
  obtain ⟨f, hf⟩ := exists_isCoord (lmG K) hπ
  obtain ⟨g, hg⟩ := exists_sylow_eq_conj_U0 hK (by omega) hf hc0 hc1 hP
  rw [← hK] at hU
  have hUeq := eq_U1_of_isFlagWG hW hf hc0 hc1 hg hU
  subst hUeq
  set U := hf.pre (gmapG g (stdF K 1)).toAddSubgroup with hUdef
  let C : Subgroup (MulAut W) :=
    { carrier := {s | s ∈ Ch11.SecA.stabW U ∧ ∀ w ∈ U, f (s w) = f w}
      mul_mem' := fun {a b} ha hb => ⟨(Ch11.SecA.stabW U).mul_mem ha.1 hb.1, fun w hw => by
        rw [MulAut.mul_apply, ha.2 _ ((Ch11.SecA.mem_stabW.mp hb.1 w).mp hw), hb.2 w hw]⟩
      one_mem' := ⟨(Ch11.SecA.stabW U).one_mem, fun w _ => rfl⟩
      inv_mem' := fun {a} ha => ⟨(Ch11.SecA.stabW U).inv_mem ha.1, fun w hw => by
        have hw' : a⁻¹ w ∈ U := (Ch11.SecA.mem_stabW.mp ((Ch11.SecA.stabW U).inv_mem ha.1) w).mp hw
        rw [← ha.2 _ hw', MulAut.apply_inv_self]⟩ }
  have hle : ⁅H ⊓ Ch11.SecA.stabW U, H ⊓ Ch11.SecA.stabW U⁆ ≤ C := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    obtain ⟨ca, hca⟩ := exists_scalar_of_mem_stabG hf hc0 hc1 g ha
    obtain ⟨cb, hcb⟩ := exists_scalar_of_mem_stabG hf hc0 hc1 g hb
    have hsa := ha.2
    have hsb := hb.2
    refine ⟨(Ch11.SecA.stabW U).mul_mem ((Ch11.SecA.stabW U).mul_mem
      ((Ch11.SecA.stabW U).mul_mem hsa hsb) ((Ch11.SecA.stabW U).inv_mem hsa))
      ((Ch11.SecA.stabW U).inv_mem hsb), fun w hw => ?_⟩
    have hU' : ∀ x, x ∈ U ↔ f x ∈ gmapG g (stdF K 1) := fun x => Iff.rfl
    have hinv : ∀ (s : MulAut W) (cs : Kˣ), s ∈ Ch11.SecA.stabW U →
        (∀ w, f w ∈ gmapG g (stdF K 1) → f (s w) = (cs : K) • f w) →
        ∀ w ∈ U, f (s⁻¹ w) = ((cs⁻¹ : Kˣ) : K) • f w := by
      intro s cs hs hcs w hw
      have hw' : s⁻¹ w ∈ U := (Ch11.SecA.mem_stabW.mp ((Ch11.SecA.stabW U).inv_mem hs) w).mp hw
      have h1 := hcs (s⁻¹ w) hw'
      rw [MulAut.apply_inv_self] at h1
      rw [h1, smul_smul, Units.inv_mul, one_smul]
    have hb1 : b⁻¹ w ∈ U := (Ch11.SecA.mem_stabW.mp ((Ch11.SecA.stabW U).inv_mem hsb) w).mp hw
    have ha1 : a⁻¹ (b⁻¹ w) ∈ U :=
      (Ch11.SecA.mem_stabW.mp ((Ch11.SecA.stabW U).inv_mem hsa) _).mp hb1
    have hb2 : b (a⁻¹ (b⁻¹ w)) ∈ U := (Ch11.SecA.mem_stabW.mp hsb _).mp ha1
    rw [commutatorElement_def, MulAut.mul_apply, MulAut.mul_apply, MulAut.mul_apply,
      hca _ ((hU' _).mp hb2), hcb _ ((hU' _).mp ha1), hinv a ca hsa hca _ hb1,
      hinv b cb hsb hcb _ hw, smul_smul, smul_smul, smul_smul]
    have : (ca : K) * ((cb : K) * (((ca⁻¹ : Kˣ) : K) * ((cb⁻¹ : Kˣ) : K))) = 1 := by
      rw [mul_left_comm (cb : K), ← mul_assoc, Units.mul_inv, one_mul, Units.mul_inv]
    rw [show (ca : K) * (cb : K) * ((ca⁻¹ : Kˣ) : K) * ((cb⁻¹ : Kˣ) : K) =
      (ca : K) * ((cb : K) * (((ca⁻¹ : Kˣ) : K) * ((cb⁻¹ : Kˣ) : K))) by ring, this, one_smul]
  intro h hh u hu
  have hC := hle ((iInf_le (derivedSeriesOf _) 1) hh)
  exact (hf.eq_iff _ _).mp (hC.2 u hu)

theorem injective_of_botG {W : Type*} [CommGroup W] {H : Subgroup (MulAut W)}
    {π : ↥⁅quasithinG2 K, quasithinG2 K⁆ →* ↥H} {f : W → (Ix3 → K)}
    (hf : IsCoord (lmG K) H ⊥ π f) {a b : W} (h : f a = f b) : a = b :=
  mul_inv_eq_one.mp (Subgroup.mem_bot.mp ((hf.eq_iff a b).mp h))

theorem factPointG2B_holds : Ch11.SecB.FactPointG2 := by
  intro K _ _ n hn hK W _ _ hW H π hπ P hP U hU
  have : CharP K 2 := charP_two_of_card (by omega) hK
  obtain ⟨c₀, hc0, hc1⟩ := exists_ne_zero_ne_one_of_card hn hK
  obtain ⟨f, hf⟩ := exists_isCoord (lmG K) hπ
  obtain ⟨g, hg⟩ := exists_sylow_eq_conj_U0 hK (by omega) hf hc0 hc1 hP
  rw [← hK] at hU
  rw [eq_U1_of_isFlagWG hW hf hc0 hc1 hg hU]
  obtain ⟨l, hl⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hmem : ∀ c : Kˣ, ((rhoG hc0 hc1 π (g * tG c * g⁻¹) : ↥H) : MulAut W) ∈
      H ⊓ Ch11.SecA.stabW (hf.pre (gmapG g (stdF K 1)).toAddSubgroup) :=
    fun c => ⟨(rhoG hc0 hc1 π _).2, mem_stab_diagG hf hc0 hc1 g c⟩
  refine ⟨⟨_, hmem l, fun s hs => ?_⟩, fun u hu w hw hu1 hw1 => ?_,
    fun s hs u hu hu1 hsu w hw => ?_⟩
  · obtain ⟨c, hc⟩ := exists_scalar_of_mem_stabG hf hc0 hc1 g hs
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hl c)
    refine ⟨k, fun u hu => injective_of_botG hf ?_⟩
    have hpow : ((rhoG hc0 hc1 π (g * tG l * g⁻¹) : ↥H) : MulAut W) ^ k =
        ((rhoG hc0 hc1 π (g * tG (l ^ k) * g⁻¹) : ↥H) : MulAut W) := by
      rw [← Subgroup.coe_zpow, ← map_zpow, conj_zpow, tG_zpow]
    rw [hc u hu, hpow, act_diagG hf hc0 hc1 g _ hu, hk]
  · obtain ⟨α, hα⟩ := mem_gmapG_stdF_one_iff.mp hu
    obtain ⟨β, hβ⟩ := mem_gmapG_stdF_one_iff.mp hw
    have hα0 : α ≠ 0 := fun h0 => hu1 (injective_of_botG hf (by rw [hα, h0, zero_smul,
      hf.map_one]))
    have hβ0 : β ≠ 0 := fun h0 => hw1 (injective_of_botG hf (by rw [hβ, h0, zero_smul,
      hf.map_one]))
    refine ⟨_, hmem (Units.mk0 (β / α) (div_ne_zero hβ0 hα0)), injective_of_botG hf ?_⟩
    rw [act_diagG hf hc0 hc1 g _ hu, Units.val_mk0, hα, hβ, smul_smul, div_mul_cancel₀ _ hα0]
  · obtain ⟨c, hc⟩ := exists_scalar_of_mem_stabG hf hc0 hc1 g hs
    have hfu0 : f u ≠ 0 := fun h0 => hu1 (injective_of_botG hf (by rw [h0, hf.map_one]))
    have hc1' : (c : K) = 1 := by
      have h1 := hc u hu
      rw [hsu] at h1
      have h2 : ((c : K) - 1) • f u = 0 := by rw [sub_smul, one_smul, ← h1, sub_self]
      exact sub_eq_zero.mp ((smul_eq_zero.mp h2).resolve_right hfu0)
    exact injective_of_botG hf (by rw [hc w hw, hc1', one_smul])

theorem factPointTG2_holds : Ch11.SecB.FactPointTG2 := by
  intro K _ _ n hn hK W _ _ hW H π hπ P hP U hU S hS2 hSH hSU
  have : CharP K 2 := charP_two_of_card (by omega) hK
  obtain ⟨c₀, hc0, hc1⟩ := exists_ne_zero_ne_one_of_card hn hK
  obtain ⟨f, hf⟩ := exists_isCoord (lmG K) hπ
  obtain ⟨g, hg⟩ := exists_sylow_eq_conj_U0 hK (by omega) hf hc0 hc1 hP
  rw [← hK] at hU
  have hUeq := eq_U1_of_isFlagWG hW hf hc0 hc1 hg hU
  refine actsCyclicallyOn_point hf (fun T hT => commutant_g2Derived hc0 hc1 _ T hT)
    (g2Act_eu_ne_zero g) (fun w => ?_) hS2 hSH hSU
  rw [hUeq]
  exact mem_gmapG_stdF_one_iff

end CFSG.Quasithin.Vol2.Ch11.G2Q8
