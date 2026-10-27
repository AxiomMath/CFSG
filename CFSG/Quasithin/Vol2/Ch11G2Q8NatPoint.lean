module

public import CFSG.Quasithin.Vol2.Ch11G2Q8Par1
public import CFSG.Quasithin.Vol2.Ch11SecSFacts4

public section

namespace CFSG.Quasithin.Vol2.Ch11.G2Q8

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall
  CFSG.Quasithin.Vol2.KGNat Matrix

variable {F : Type} [Field F] [CharP F 2]

theorem fixed_U0 {x : Ix3 → F} (hx : ∀ u ∈ U0 F, g2Act u x = x) : x ∈ stdF F 1 := by
  have h1 := hx _ (g2X_mem_U0 1)
  have h2 := hx _ (g2Y_mem_U0 1 0)
  have h3 := hx _ (g2Y_mem_U0 0 1)
  rw [q6_eta x, g2Act_x0q] at h1
  rw [q6_eta x, g2Act_y12q] at h2 h3
  obtain ⟨e0, -, -, -, e4, e5⟩ := q6_inj h1
  obtain ⟨f0, -, -, -, -, -⟩ := q6_inj h2
  obtain ⟨g0, -, -, -, -, -⟩ := q6_inj h3
  rw [mem_stdF]
  conv => rw [q6_eta x]
  rw [inF_q6_iff]
  refine ⟨by omega, fun _ => ?_, fun _ => ?_, fun _ => ?_, fun _ => ?_, fun _ => ?_⟩
  · linear_combination e5
  · linear_combination e4
  · linear_combination e0
  · linear_combination g0
  · linear_combination f0

theorem g2Act_tG (c : Fˣ) (w : Ix3 → F) :
    g2Act (tG c) w = q6 ((c : F) * w (.inl 0)) (((c⁻¹ : Fˣ) : F) * w (.inl 1)) (w (.inl 2))
      (((c⁻¹ : Fˣ) : F) * w (.inr 0)) ((c : F) * w (.inr 1))
      ((c : F) * ((c⁻¹ : Fˣ) : F) * w (.inr 2)) := by
  conv_lhs => rw [q6_eta w]
  rw [tG, g2Act_diag3]
  refine q6_congr rfl rfl (one_mul _) ?_ ?_ ?_ <;> ring

theorem tG_inF (c : Fˣ) {h : ℕ} (w : Ix3 → F) : InF h (g2Act (tG c) w) ↔ InF h w := by
  have hc : (c : F) ≠ 0 := c.ne_zero
  have hci : ((c⁻¹ : Fˣ) : F) ≠ 0 := (c⁻¹).ne_zero
  rw [g2Act_tG]
  conv_rhs => rw [q6_eta w]
  rw [inF_q6_iff, inF_q6_iff]
  simp only [mul_eq_zero, hc, hci, false_or]

theorem tG_conj_mem_U0 (c : Fˣ) {u : ↥(cayleyGroup F)} (hu : u ∈ U0 F) :
    tG c * u * (tG c)⁻¹ ∈ U0 F := by
  refine mem_U0.mpr fun h w hw => ?_
  rw [tG_inv, g2Act_mul_apply, g2Act_mul_apply]
  have h1 : InF (h + 1) (g2Act (tG c⁻¹) w) := (tG_inF _ w).mpr hw
  have h2 := (mem_U0.mp hu) h _ h1
  have e : g2Act (tG c) (g2Act u (g2Act (tG c⁻¹) w)) - w =
      g2Act (tG c) (g2Act u (g2Act (tG c⁻¹) w) - g2Act (tG c⁻¹) w) := by
    rw [map_sub, ← tG_inv, g2Act_apply_inv]
  rw [e]
  exact (tG_inF c _).mpr h2

theorem tG_mem_normalizer_U0 (c : Fˣ) :
    tG c ∈ Subgroup.normalizer (U0 F : Set ↥(cayleyGroup F)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro u
  refine ⟨tG_conj_mem_U0 c, fun h => ?_⟩
  have h1 := tG_conj_mem_U0 c⁻¹ h
  rwa [← tG_inv, inv_inv, show (tG c)⁻¹ * (tG c * u * (tG c)⁻¹) * tG c = u by group] at h1

theorem factNatPointG2_holds : Ch11.SecS.FactNatPointG2 := by
  intro K _ _ n hn hK W _ _ hW H π hπ P hP U₁ hU₁ D hD
  have : CharP K 2 := KGNat.charP_two_of_card (by omega) hK
  have : Finite (MulAut W) := Finite.of_injective _ MulEquiv.toEquiv_injective
  obtain ⟨c₀, hc0, hc1⟩ := exists_ne_zero_ne_one_of_card hn hK
  obtain ⟨f, hf⟩ := exists_isCoord (lmG K) hπ
  have hinj : ∀ a b : W, f a = f b → a = b := fun a b h => injective_of_botG hf h
  obtain ⟨g, hg⟩ := exists_sylow_eq_conj_U0 hK (by omega) hf hc0 hc1 hP
  have hU' : Ch11.SecA.IsFlagW H P ⊥ (Nat.card K) 1 U₁ := by rw [hK]; exact hU₁
  have hUeq := eq_U1_of_isFlagWG hW hf hc0 hc1 hg hU'
  subst hUeq
  set U₁ := hf.pre (gmapG g (stdF K 1)).toAddSubgroup with hU₁def
  have hmemU : ∀ w, w ∈ U₁ ↔ f w ∈ gmapG g (stdF K 1) := fun w => Iff.rfl
  have hPU : ∀ w, (∀ p ∈ P, p w = w) ↔ w ∈ U₁ := by
    intro w
    constructor
    · intro h
      rw [hmemU, mem_gmapG]
      refine fixed_U0 fun u hu => ?_
      have h1 := h _ ((hg _).mpr ⟨u, hu, rfl⟩)
      have h2 := congrArg f h1
      rw [IsCoord.actG hf hc0 hc1] at h2
      have h3 := congrArg (g2Act g⁻¹) h2
      rw [conj_g2Act] at h3
      exact h3
    · intro hw p hp
      obtain ⟨u, hu, rfl⟩ := (hg p).mp hp
      apply hinj
      obtain ⟨t, ht⟩ := mem_gmapG_stdF_one_iff.mp ((hmemU w).mp hw)
      rw [IsCoord.actG hf hc0 hc1, ht, g2Act_smul, g2Act_mul_apply, g2Act_mul_apply,
        g2Act_inv_apply, show g2Act u (eu 0 1) = eu 0 1 from U0_le_stabV0 hu]
  refine ⟨fun w hw1 hwP => ⟨(hPU w).mp hwP, fun h hh hhw => ?_⟩, ?_⟩
  · obtain ⟨t, ht⟩ := mem_gmapG_stdF_one_iff.mp ((hmemU w).mp ((hPU w).mp hwP))
    have ht0 : t ≠ 0 := by
      rintro rfl
      rw [zero_smul] at ht
      exact hw1 (hinj _ _ (by rw [ht, hf.map_one]))
    obtain ⟨M, hM⟩ := (rhoG_bijective hf hc0 hc1).2 ⟨h, hh⟩
    have hhM : h = ((rhoG hc0 hc1 π M : ↥H) : MulAut W) := by rw [hM]
    have hMg : g2Act M (g2Act g (eu 0 1)) = g2Act g (eu 0 1) := by
      have h1 := congrArg f hhw
      rw [hhM, IsCoord.actG hf hc0 hc1, ht, g2Act_smul] at h1
      exact smul_right_injective _ ht0 h1
    have hMg' : g2Act M⁻¹ (g2Act g (eu 0 1)) = g2Act g (eu 0 1) := by
      conv_lhs => rw [← hMg]
      rw [g2Act_inv_apply]
    rw [hhM, IsCoord.rhoG_mem_stabW_iff hf hc0 hc1 (hf.le_pre _), hf.img_pre]
    intro y
    change y ∈ gmapG g _ ↔ _ ∈ gmapG g _
    rw [mem_gmapG_stdF_one_iff, mem_gmapG_stdF_one_iff]
    constructor
    · rintro ⟨s, rfl⟩
      exact ⟨s, by rw [g2Act_smul, hMg]⟩
    · rintro ⟨s, hs⟩
      refine ⟨s, ?_⟩
      rw [← g2Act_inv_apply M y, hs, g2Act_smul, hMg']
  · set B := H ⊓ Subgroup.normalizer (P : Set (MulAut W)) with hB
    have hBU : ∀ b ∈ B, ∀ w ∈ U₁, b w ∈ U₁ := by
      intro b hb w hw
      rw [← hPU] at hw ⊢
      intro p hp
      have hp' : b⁻¹ * p * b⁻¹⁻¹ ∈ P :=
        (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hb.2) p).mp hp
      have h1 := hw _ hp'
      rw [MulAut.mul_apply, MulAut.mul_apply, inv_inv] at h1
      calc p (b w) = b (b⁻¹ (p (b w))) := (MulAut.apply_inv_self W b _).symm
        _ = b w := by rw [h1]
    have hBstab : ∀ b ∈ B, b ∈ H ⊓ Ch11.SecA.stabW U₁ := by
      intro b hb
      refine ⟨hb.1, Ch11.SecA.mem_stabW.mpr fun w => ⟨hBU b hb w, fun h => ?_⟩⟩
      have h1 := hBU b⁻¹ (B.inv_mem hb) _ h
      rwa [MulAut.inv_apply_self] at h1
    have hscal : ∀ b ∈ B, ∃ c : K, ∀ u ∈ U₁, f (b u) = c • f u := by
      intro b hb
      obtain ⟨c, hc⟩ := exists_scalar_of_mem_stabG hf hc0 hc1 g (hBstab b hb)
      exact ⟨c, fun u hu => hc u hu⟩
    let K₀ : Subgroup (MulAut W) :=
      { carrier := {b | b ∈ B ∧ ∀ u ∈ U₁, b u = u}
        mul_mem' := fun {x y} hx hy => ⟨B.mul_mem hx.1 hy.1, fun u hu => by
          rw [MulAut.mul_apply, hy.2 u hu, hx.2 u hu]⟩
        one_mem' := ⟨B.one_mem, fun u _ => rfl⟩
        inv_mem' := fun {x} hx => ⟨B.inv_mem hx.1, fun u hu => by
          conv_lhs => rw [← hx.2 u hu]
          exact MulAut.inv_apply_self W x u⟩ }
    have hK₀B : K₀ ≤ B := fun x hx => hx.1
    have hK₀n : (K₀.subgroupOf B).Normal := by
      refine ⟨fun x hx b => ?_⟩
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      refine ⟨B.mul_mem (B.mul_mem b.2 hx.1) (B.inv_mem b.2), fun u hu => ?_⟩
      have hbu : (b : MulAut W)⁻¹ u ∈ U₁ := hBU _ (B.inv_mem b.2) u hu
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, MulAut.mul_apply,
        MulAut.mul_apply, hx.2 _ hbu, MulAut.apply_inv_self]
    by_contra hcon
    push Not at hcon
    have hDK : D ≤ K₀ := by
      intro d hd
      obtain ⟨u, hu, hu1, hdu⟩ := hcon d hd
      have hdB : d ∈ B := hD.1 hd
      obtain ⟨c, hc⟩ := hscal d hdB
      have hfu : f u ≠ 0 := fun h0 => hu1 (hinj _ _ (by rw [h0, hf.map_one]))
      have hc1' : c = 1 := by
        have h1 := hc u hu
        rw [hdu] at h1
        have h2 : (c - 1) • f u = 0 := by rw [sub_smul, ← h1, one_smul, sub_self]
        exact sub_eq_zero.mp ((smul_eq_zero.mp h2).resolve_right hfu)
      exact ⟨hdB, fun v hv => hinj _ _ (by rw [hc v hv, hc1', one_smul])⟩
    obtain ⟨k, hk⟩ := hD.2.2
    have hdiv : K₀.relIndex B ∣ 2 ^ k := by
      rw [← hk, ← Subgroup.relIndex_mul_relIndex D K₀ B hDK hK₀B]
      exact Dvd.intro_left _ rfl
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdiv
    obtain ⟨a, ha⟩ := IsCyclic.exists_generator (α := Kˣ)
    have ha1 : (a : K) ≠ 1 := by
      intro h
      have ha1' : a = 1 := Units.ext h
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (ha (Units.mk0 c₀ hc0))
      rw [ha1', _root_.one_zpow] at hk
      exact hc1 (congrArg Units.val hk).symm
    set t := ((rhoG hc0 hc1 π (g * tG a * g⁻¹) : ↥H) : MulAut W) with ht
    have e1 : ∀ X Y : ↥(cayleyGroup K), ((rhoG hc0 hc1 π X : ↥H) : MulAut W) *
        ((rhoG hc0 hc1 π Y : ↥H) : MulAut W) * ((rhoG hc0 hc1 π X : ↥H) : MulAut W)⁻¹ =
        ((rhoG hc0 hc1 π (X * Y * X⁻¹) : ↥H) : MulAut W) := fun X Y => by
      simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]
    have e2 : ∀ X Y : ↥(cayleyGroup K), ((rhoG hc0 hc1 π X : ↥H) : MulAut W)⁻¹ *
        ((rhoG hc0 hc1 π Y : ↥H) : MulAut W) * ((rhoG hc0 hc1 π X : ↥H) : MulAut W) =
        ((rhoG hc0 hc1 π (X⁻¹ * Y * X) : ↥H) : MulAut W) := fun X Y => by
      simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]
    have htN : t ∈ Subgroup.normalizer (P : Set (MulAut W)) := by
      have hTN := tG_mem_normalizer_U0 a
      rw [Subgroup.mem_normalizer_iff]
      intro y
      constructor
      · intro hy
        obtain ⟨u, hu, rfl⟩ := (hg y).mp hy
        refine (hg _).mpr ⟨tG a * u * (tG a)⁻¹,
          (Subgroup.mem_normalizer_iff.mp hTN u).mp hu, ?_⟩
        rw [ht, e1]
        congr 2
        group
      · intro hy
        obtain ⟨u, hu, hu'⟩ := (hg _).mp hy
        refine (hg y).mpr ⟨(tG a)⁻¹ * u * tG a, ?_, ?_⟩
        · refine (Subgroup.mem_normalizer_iff.mp hTN _).mpr ?_
          rwa [show tG a * ((tG a)⁻¹ * u * tG a) * (tG a)⁻¹ = u by group]
        · have h1 : y = t⁻¹ * (t * y * t⁻¹) * t := by group
          rw [h1, hu', ht, e2]
          congr 2
          group
    have htB : t ∈ B := ⟨(rhoG hc0 hc1 π _).2, htN⟩
    have htf : ∀ u ∈ U₁, f (t u) = (a : K) • f u := fun u hu => act_diagG hf hc0 hc1 g a hu
    have htk : ∀ m : ℕ, ∀ u ∈ U₁, f ((t ^ m) u) = ((a : K) ^ m) • f u := by
      intro m
      induction m with
      | zero => intro u hu; rw [pow_zero, MulAut.one_apply, pow_zero, one_smul]
      | succ m ih =>
        intro u hu
        rw [pow_succ', MulAut.mul_apply, htf _ (hBU _ (B.pow_mem htB m) u hu), ih u hu,
          smul_smul, pow_succ']
    have hpow : ((⟨t, htB⟩ : ↥B) ^ 2 ^ j) ∈ K₀.subgroupOf B := by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
      have h1 := pow_card_eq_one' (x := (QuotientGroup.mk ⟨t, htB⟩ : ↥B ⧸ K₀.subgroupOf B))
      rwa [← Subgroup.index, ← Subgroup.relIndex, hj] at h1
    obtain ⟨u₀, hu₀⟩ := hf.surj (g2Act g (eu 0 1))
    have hu₀U : u₀ ∈ U₁ := mem_gmapG_stdF_one_iff.mpr ⟨1, by rw [hu₀, one_smul]⟩
    have h2 := (Subgroup.mem_subgroupOf.mp hpow).2 u₀ hu₀U
    rw [Subgroup.coe_pow] at h2
    have h3 := htk (2 ^ j) u₀ hu₀U
    rw [h2, hu₀] at h3
    have h4 : ((a : K) ^ 2 ^ j - 1) • g2Act g (eu 0 (1 : K)) = 0 := by
      rw [sub_smul, ← h3, one_smul, sub_self]
    have h5 : (a : K) ^ 2 ^ j = 1 :=
      sub_eq_zero.mp ((smul_eq_zero.mp h4).resolve_right (g2Act_eu_ne_zero g))
    exact ha1 (eq_one_of_pow_two_pow h5)

end CFSG.Quasithin.Vol2.Ch11.G2Q8
