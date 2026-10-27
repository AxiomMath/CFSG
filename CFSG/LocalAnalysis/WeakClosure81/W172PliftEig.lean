module

public import CFSG.LocalAnalysis.WeakClosure81.W172PliftVec
public import CFSG.GH74.GLS.C3.Layer1.Th2A7ExcLift
public import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.LocalAnalysis.WeakClosure81

variable {Γ : Type} [Group Γ] [Finite Γ]

structure W172PliftSetup (p : ℕ) (P N : Subgroup Γ) (D : Finset Γ) : Prop where
  prime : p.Prime
  odd : p ≠ 2
  pgroup : IsPGroup p P
  le : N ≤ P
  n_norm : ∀ x ∈ P, ∀ n ∈ N, x * n * x⁻¹ ∈ N
  abelian : ∀ x ∈ P, ∀ y ∈ P, x * y * x⁻¹ * y⁻¹ ∈ N
  sq : ∀ e ∈ D, e * e = 1
  comm : ∀ e ∈ D, ∀ f ∈ D, e * f = f * e
  norm_p : ∀ e ∈ D, ∀ x ∈ P, e * x * e⁻¹ ∈ P
  norm_n : ∀ e ∈ D, ∀ n ∈ N, e * n * e⁻¹ ∈ N
  acts : ∀ e ∈ D, ∃ x ∈ P, e * x * e⁻¹ * x⁻¹ ∉ N
  no_two_inverted : ∀ e ∈ D, ∀ f ∈ D, e ≠ f → ∀ u ∈ P,
    e * u * e⁻¹ = u⁻¹ → f * u * f⁻¹ = u⁻¹ → u = 1

private theorem w172_exists_fixed_mem_coset {K N : Subgroup Γ} {x₀ : Γ}
    (hK : IsPGroup 2 ↥K) (hNodd : Odd (Nat.card ↥N))
    (hKN : K ≤ Subgroup.normalizer (N : Set Γ))
    (hstab : ∀ k ∈ K, x₀⁻¹ * (k * x₀ * k⁻¹) ∈ N) :
    ∃ w : Γ, x₀⁻¹ * w ∈ N ∧ ∀ k ∈ K, k * w * k⁻¹ = w := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let α := {w : Γ // x₀⁻¹ * w ∈ N}
  have hcard : Nat.card α = Nat.card ↥N := by
    refine Nat.card_congr ?_
    exact
      { toFun := fun w => ⟨x₀⁻¹ * (w : Γ), w.2⟩
        invFun := fun n => ⟨x₀ * (n : Γ), by
          show x₀⁻¹ * (x₀ * (n : Γ)) ∈ N
          rw [← mul_assoc, inv_mul_cancel, one_mul]
          exact n.2⟩
        left_inv := fun w => by
          apply Subtype.ext
          show x₀ * (x₀⁻¹ * (w : Γ)) = (w : Γ)
          rw [← mul_assoc, mul_inv_cancel, one_mul]
        right_inv := fun n => by
          apply Subtype.ext
          show x₀⁻¹ * (x₀ * (n : Γ)) = (n : Γ)
          rw [← mul_assoc, inv_mul_cancel, one_mul] }
  have hnot : ¬ 2 ∣ Nat.card α := by
    rw [hcard]
    exact fun h2 => (Nat.not_even_iff_odd.2 hNodd) (even_iff_two_dvd.2 h2)
  letI : SMul ↥K α :=
    ⟨fun k w => ⟨(k : Γ) * (w : Γ) * (k : Γ)⁻¹, by
      have hm : (k : Γ) * (x₀⁻¹ * (w : Γ)) * (k : Γ)⁻¹ ∈ N :=
        (Subgroup.le_normalizer_iff.1 hKN) k k.2 _ w.2
      have hc : x₀⁻¹ * ((k : Γ) * x₀ * (k : Γ)⁻¹) ∈ N := hstab k k.2
      have heq : x₀⁻¹ * ((k : Γ) * (w : Γ) * (k : Γ)⁻¹) =
          (x₀⁻¹ * ((k : Γ) * x₀ * (k : Γ)⁻¹)) *
            ((k : Γ) * (x₀⁻¹ * (w : Γ)) * (k : Γ)⁻¹) := by group
      rw [heq]
      exact N.mul_mem hc hm⟩⟩
  letI : MulAction ↥K α :=
    { one_smul := fun w => Subtype.ext (by
        show (1 : Γ) * (w : Γ) * (1 : Γ)⁻¹ = (w : Γ)
        simp)
      mul_smul := fun a b w => Subtype.ext (by
        show ((a : Γ) * (b : Γ)) * (w : Γ) * ((a : Γ) * (b : Γ))⁻¹ =
          (a : Γ) * ((b : Γ) * (w : Γ) * (b : Γ)⁻¹) * (a : Γ)⁻¹
        group) }
  obtain ⟨w, hw⟩ := hK.nonempty_fixed_point_of_prime_not_dvd_card α hnot
  refine ⟨(w : α).1, (w : α).2, fun k hk => ?_⟩
  have hfix := MulAction.mem_fixedPoints.mp hw (⟨k, hk⟩ : ↥K)
  exact congrArg Subtype.val hfix

private lemma w172_conj_mem_centralizer {S : Set Γ} {a y : Γ}
    (ha : ∀ s ∈ S, a * s = s * a) (hay : ∀ s ∈ S, a⁻¹ * s = s * a⁻¹)
    (hy : y ∈ Subgroup.centralizer S) :
    a * y * a⁻¹ ∈ Subgroup.centralizer S := by
  rw [Subgroup.mem_centralizer_iff] at hy ⊢
  intro s hs
  calc s * (a * y * a⁻¹) = (s * a) * y * a⁻¹ := by group
    _ = (a * s) * y * a⁻¹ := by rw [← ha s hs]
    _ = a * (s * y) * a⁻¹ := by group
    _ = a * (y * s) * a⁻¹ := by rw [hy s hs]
    _ = (a * y) * (s * a⁻¹) := by group
    _ = (a * y) * (a⁻¹ * s) := by rw [← hay s hs]
    _ = (a * y * a⁻¹) * s := by group
theorem w172_plift_eig_lift {p : ℕ} {P N : Subgroup Γ} {D : Finset Γ}
    (h : W172PliftSetup p P N D) {e : Γ} (he : e ∈ D) :
    ∃ y ∈ P, y ≠ 1 ∧ y ^ p = 1 ∧ e * y * e⁻¹ = y⁻¹ ∧ ∀ f ∈ D, f ≠ e → f * y * f⁻¹ = y := by
  classical
  have hpodd : Odd p := h.prime.odd_of_ne_two h.odd
  let F : Subgroup Γ := Subgroup.closure (D : Set Γ)
  have heF : e ∈ F := Subgroup.subset_closure he
  have hFEA : CFSG.Open.IsElemAbelian 2 F :=
    CFSG.Open.IsElemAbelian.closure_of_commute (s := (D : Set Γ))
      (fun a ha b hb => h.comm a ha b hb)
      (fun a ha => by rw [pow_two]; exact h.sq a ha)
  have hF2 : IsPGroup 2 ↥F := by
    intro x
    refine ⟨1, Subtype.ext ?_⟩
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    rw [pow_one, pow_two]
    exact hFEA.mul_self_eq_one x.2
  have hFN : F ≤ Subgroup.normalizer (N : Set Γ) := by
    rw [Subgroup.closure_le]
    intro d hd
    refine Subgroup.mem_normalizer_iff.2 ?_
    intro n
    exact ⟨fun hn => h.norm_n d hd n hn, fun hn => by
      have h1 : d * (d * n * d⁻¹) * d⁻¹ ∈ N := h.norm_n d hd _ hn
      rwa [show d * (d * n * d⁻¹) * d⁻¹ = n by
        calc d * (d * n * d⁻¹) * d⁻¹ = (d * d) * n * (d * d)⁻¹ := by group
          _ = n := by rw [h.sq d hd]; group] at h1⟩
  have hPN : P ≤ Subgroup.normalizer (N : Set Γ) := by
    rw [Subgroup.le_normalizer_iff]
    exact fun x hx n hn => h.n_norm x hx n hn
  let NP : Subgroup ↥P := N.subgroupOf P
  haveI hNP : NP.Normal :=
    (Subgroup.normal_subgroupOf_iff h.le).2 fun n x hn hx => h.n_norm x hx n hn
  let Q := ↥P ⧸ NP
  have hQcomm : ∀ a b : Q, a * b = b * a := by
    intro a b
    induction a using QuotientGroup.induction_on with
    | H x =>
      induction b using QuotientGroup.induction_on with
      | H y =>
        show (x : Q) * (y : Q) = (y : Q) * (x : Q)
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
        apply QuotientGroup.eq.2
        rw [Subgroup.mem_subgroupOf]
        have hmem : ((y : Γ)⁻¹ * (x : Γ)⁻¹ * (y : Γ) * (x : Γ)) ∈ N := by
          have hc : (x : Γ) * (y : Γ) * (x : Γ)⁻¹ * (y : Γ)⁻¹ ∈ N :=
            h.abelian x x.2 y y.2
          have h1 : (x : Γ)⁻¹ * ((x : Γ) * (y : Γ) * (x : Γ)⁻¹ * (y : Γ)⁻¹) *
              (x : Γ) ∈ N := by
            simpa using h.n_norm (x : Γ)⁻¹ (P.inv_mem x.2) _ hc
          have h2 : (y : Γ) * (x : Γ)⁻¹ * (y : Γ)⁻¹ * (x : Γ) ∈ N := by
            convert h1 using 1 <;> group
          have h3 : ((y : Γ) * (x : Γ)⁻¹ * (y : Γ)⁻¹ * (x : Γ))⁻¹ ∈ N := N.inv_mem h2
          have h4 : (y : Γ)⁻¹ * ((y : Γ) * (x : Γ)⁻¹ * (y : Γ)⁻¹ * (x : Γ))⁻¹ *
              (y : Γ) ∈ N := by
            simpa using h.n_norm (y : Γ)⁻¹ (P.inv_mem y.2) _ h3
          convert h4 using 1 <;> group
        convert hmem using 1 <;> (simp only [Subgroup.coe_mul, Subgroup.coe_inv]; group)
  letI : CommGroup Q := { (inferInstance : Group Q) with mul_comm := hQcomm }
  haveI : Fact p.Prime := ⟨h.prime⟩
  have hQp : IsPGroup p Q := h.pgroup.to_quotient NP
  have hnoinvol : ∀ q : Q, q * q = 1 → q = 1 := by
    intro q hq
    have h2 : orderOf q ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hq)
    obtain ⟨k, hk⟩ := hQp.exists_orderOf_dvd_pow q
    have hcop : Nat.Coprime 2 (p ^ k) := Nat.coprime_two_left.2 (hpodd.pow)
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop h2 hk)
  let φ : ↥D → ↥P →* ↥P := fun f =>
    { toFun := fun x => ⟨f.val * (x : Γ) * f.val⁻¹, h.norm_p f.val f.2 x x.2⟩
      map_one' := by ext; simp
      map_mul' := by intro x y; ext; simp only [Subgroup.coe_mul]; group }
  let Gf : ↥D → Q →* Q := fun f =>
    QuotientGroup.map NP NP (φ f) (fun x hx => by
      rw [Subgroup.mem_comap]
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      exact h.norm_n f.val f.2 (x : Γ) hx)
  have hGf2 : ∀ (f : ↥D) (x : Q), Gf f (Gf f x) = x := by
    intro f x
    induction x using QuotientGroup.induction_on with
    | H y =>
      show Gf f (Gf f ((y : ↥P) : Q)) = ((y : ↥P) : Q)
      simp only [Gf, QuotientGroup.map_mk]
      apply congrArg (fun z : ↥P => (z : Q))
      ext
      show f.val * (f.val * (y : Γ) * f.val⁻¹) * f.val⁻¹ = (y : Γ)
      calc f.val * (f.val * (y : Γ) * f.val⁻¹) * f.val⁻¹
          = (f.val * f.val) * (y : Γ) * (f.val * f.val)⁻¹ := by group
        _ = (y : Γ) := by rw [h.sq f.val f.2]; group
  have hGfc : ∀ (f g : ↥D) (x : Q), Gf f (Gf g x) = Gf g (Gf f x) := by
    intro f g x
    induction x using QuotientGroup.induction_on with
    | H y =>
      show Gf f (Gf g ((y : ↥P) : Q)) = Gf g (Gf f ((y : ↥P) : Q))
      simp only [Gf, QuotientGroup.map_mk]
      apply congrArg (fun z : ↥P => (z : Q))
      ext
      show f.val * (g.val * (y : Γ) * g.val⁻¹) * f.val⁻¹ =
        g.val * (f.val * (y : Γ) * f.val⁻¹) * g.val⁻¹
      calc f.val * (g.val * (y : Γ) * g.val⁻¹) * f.val⁻¹
          = (f.val * g.val) * (y : Γ) * (f.val * g.val)⁻¹ := by group
        _ = (g.val * f.val) * (y : Γ) * (g.val * f.val)⁻¹ := by
            rw [h.comm f.val f.2 g.val g.2]
        _ = g.val * (f.val * (y : Γ) * f.val⁻¹) * g.val⁻¹ := by group
  have hact : ∃ x ∈ (⊤ : Subgroup Q), Gf ⟨e, he⟩ x ≠ x := by
    obtain ⟨x, hxP, hxN⟩ := h.acts e he
    refine ⟨((⟨x, hxP⟩ : ↥P) : Q), Subgroup.mem_top _, ?_⟩
    intro hcon
    apply hxN
    simp only [Gf, QuotientGroup.map_mk] at hcon
    have hmem : ((φ ⟨e, he⟩ ⟨x, hxP⟩)⁻¹ * ⟨x, hxP⟩ : ↥P) ∈ NP :=
      QuotientGroup.eq.1 hcon
    rw [Subgroup.mem_subgroupOf] at hmem
    have haP : e * x * e⁻¹ ∈ P := h.norm_p e he x hxP
    have h1 : (e * x * e⁻¹)⁻¹ * x ∈ N := by simpa [φ] using hmem
    have h2 : x⁻¹ * (e * x * e⁻¹) ∈ N := by simpa using N.inv_mem h1
    have h3 : (e * x * e⁻¹) * (x⁻¹ * (e * x * e⁻¹)) * (e * x * e⁻¹)⁻¹ ∈ N :=
      (Subgroup.le_normalizer_iff.1 hPN) (e * x * e⁻¹) haP _ h2
    have h4 : (e * x * e⁻¹) * x⁻¹ ∈ N := by convert h3 using 1 <;> group
    simpa using h4
  obtain ⟨q, _, hq1, hqinv, hw⟩ :=
    w172_plift_eig_inverted (⊤ : Subgroup Q) (fun w _ hw => hnoinvol w hw)
      Finset.univ Gf (fun i _ w _ => Subgroup.mem_top w)
      (fun i _ j _ x => hGfc i j x) (fun i _ x => hGf2 i x)
      (i₀ := ⟨e, he⟩) (Finset.mem_univ _) hact
  obtain ⟨x₀, hx₀⟩ := QuotientGroup.mk'_surjective NP q
  have hx₀Q : ((x₀ : ↥P) : Q) = q := hx₀
  let K : Subgroup Γ :=
    { carrier := {k | k ∈ F ∧ (x₀ : Γ)⁻¹ * (k * (x₀ : Γ) * k⁻¹) ∈ N}
      one_mem' := ⟨F.one_mem, by simpa using N.one_mem⟩
      mul_mem' := by
        rintro k l ⟨hkF, hk⟩ ⟨hlF, hl⟩
        refine ⟨F.mul_mem hkF hlF, ?_⟩
        rw [show (x₀ : Γ)⁻¹ * ((k * l) * (x₀ : Γ) * (k * l)⁻¹) =
            ((x₀ : Γ)⁻¹ * (k * (x₀ : Γ) * k⁻¹)) *
              (k * ((x₀ : Γ)⁻¹ * (l * (x₀ : Γ) * l⁻¹)) * k⁻¹) by group]
        exact N.mul_mem hk ((Subgroup.le_normalizer_iff.1 hFN) k hkF _ hl)
      inv_mem' := by
        rintro k ⟨hkF, hk⟩
        refine ⟨F.inv_mem hkF, ?_⟩
        have h1 : k⁻¹ * ((x₀ : Γ)⁻¹ * (k * (x₀ : Γ) * k⁻¹)) * k ∈ N := by
          simpa using (Subgroup.le_normalizer_iff.1 hFN) k⁻¹ (F.inv_mem hkF) _ hk
        have h2 : (k⁻¹ * ((x₀ : Γ)⁻¹ * (k * (x₀ : Γ) * k⁻¹)) * k)⁻¹ ∈ N := N.inv_mem h1
        convert h2 using 1 <;> group }
  have hmemK_fix : ∀ (f : Γ) (hf : f ∈ D), Gf ⟨f, hf⟩ q = q → f ∈ K := by
    intro f hf hfix
    refine ⟨Subgroup.subset_closure hf, ?_⟩
    have hfix' : Gf ⟨f, hf⟩ ((x₀ : ↥P) : Q) = ((x₀ : ↥P) : Q) := by
      rw [hx₀Q]; exact hfix
    simp only [Gf, QuotientGroup.map_mk] at hfix'
    have hmem : ((φ ⟨f, hf⟩ x₀)⁻¹ * x₀ : ↥P) ∈ NP := QuotientGroup.eq.1 hfix'
    rw [Subgroup.mem_subgroupOf] at hmem
    have hmem' : (f * (x₀ : Γ) * f⁻¹)⁻¹ * (x₀ : Γ) ∈ N := by
      simpa [φ] using hmem
    convert N.inv_mem hmem' using 1 <;> group
  have hmemK_inv : ∀ (f : Γ) (hf : f ∈ D), Gf ⟨f, hf⟩ q = q⁻¹ → e * f ∈ K := by
    intro f hf hinv
    refine ⟨F.mul_mem heF (Subgroup.subset_closure hf), ?_⟩
    have hinv' : Gf ⟨f, hf⟩ ((x₀ : ↥P) : Q) = ((x₀ : ↥P) : Q)⁻¹ := by
      rw [hx₀Q]; exact hinv
    simp only [Gf, QuotientGroup.map_mk] at hinv'
    have hinvP : ((φ ⟨f, hf⟩ x₀)⁻¹ * x₀⁻¹ : ↥P) ∈ NP := QuotientGroup.eq.1 hinv'
    rw [Subgroup.mem_subgroupOf] at hinvP
    have hfmem : f * (x₀ : Γ) * f⁻¹ * (x₀ : Γ) ∈ N := by
      have hmem0 : ((f * (x₀ : Γ) * f⁻¹)⁻¹ * (x₀ : Γ)⁻¹) ∈ N := by
        simpa [φ] using hinvP
      have hinvmem : (x₀ : Γ) * (f * (x₀ : Γ) * f⁻¹) ∈ N := by
        simpa using N.inv_mem hmem0
      have haP : f * (x₀ : Γ) * f⁻¹ ∈ P := h.norm_p f hf (x₀ : Γ) x₀.2
      have hconj : (f * (x₀ : Γ) * f⁻¹) * ((x₀ : Γ) * (f * (x₀ : Γ) * f⁻¹)) *
          (f * (x₀ : Γ) * f⁻¹)⁻¹ ∈ N :=
        (Subgroup.le_normalizer_iff.1 hPN) _ haP _ hinvmem
      convert hconj using 1 <;> group
    have hqinv' : Gf ⟨e, he⟩ ((x₀ : ↥P) : Q) = ((x₀ : ↥P) : Q)⁻¹ := by
      rw [hx₀Q]; exact hqinv
    simp only [Gf, QuotientGroup.map_mk] at hqinv'
    have heinvP : ((φ ⟨e, he⟩ x₀)⁻¹ * x₀⁻¹ : ↥P) ∈ NP := QuotientGroup.eq.1 hqinv'
    rw [Subgroup.mem_subgroupOf] at heinvP
    have hemem : e * (x₀ : Γ) * e⁻¹ * (x₀ : Γ) ∈ N := by
      have hmem0 : ((e * (x₀ : Γ) * e⁻¹)⁻¹ * (x₀ : Γ)⁻¹) ∈ N := by
        simpa [φ] using heinvP
      have hinvmem : (x₀ : Γ) * (e * (x₀ : Γ) * e⁻¹) ∈ N := by
        simpa using N.inv_mem hmem0
      have haP : e * (x₀ : Γ) * e⁻¹ ∈ P := h.norm_p e he (x₀ : Γ) x₀.2
      have hconj : (e * (x₀ : Γ) * e⁻¹) * ((x₀ : Γ) * (e * (x₀ : Γ) * e⁻¹)) *
          (e * (x₀ : Γ) * e⁻¹)⁻¹ ∈ N :=
        (Subgroup.le_normalizer_iff.1 hPN) _ haP _ hinvmem
      convert hconj using 1 <;> group
    have h1 : e * (f * (x₀ : Γ) * f⁻¹ * (x₀ : Γ)) * e⁻¹ ∈ N := h.norm_n e he _ hfmem
    have hgoal : (e * f) * (x₀ : Γ) * (e * f)⁻¹ =
        (e * (f * (x₀ : Γ) * f⁻¹ * (x₀ : Γ)) * e⁻¹) * (x₀ : Γ) *
          (e * (x₀ : Γ) * e⁻¹ * (x₀ : Γ))⁻¹ := by group
    rw [hgoal]
    have h2 : (x₀ : Γ)⁻¹ * (e * (f * (x₀ : Γ) * f⁻¹ * (x₀ : Γ)) * e⁻¹) *
        (x₀ : Γ) ∈ N := by
      simpa using h.n_norm (x₀ : Γ)⁻¹ (P.inv_mem x₀.2) _ h1
    convert N.mul_mem h2 (N.inv_mem hemem) using 1 <;> group
  have hPodd : Odd (Nat.card ↥P) := by
    obtain ⟨n, hn⟩ := h.pgroup.exists_card_eq
    rw [hn]
    exact hpodd.pow
  have hNodd : Odd (Nat.card ↥N) :=
    hPodd.of_dvd_nat (Subgroup.card_dvd_of_le h.le)
  have hK2 : IsPGroup 2 ↥K := hF2.to_le (fun k hk => hk.1)
  have hKN : K ≤ Subgroup.normalizer (N : Set Γ) := fun k hk => hFN hk.1
  obtain ⟨x₁, hx₁coset, hx₁K⟩ :=
    w172_exists_fixed_mem_coset hK2 hNodd hKN (fun k hk => hk.2)
  let Y : Subgroup Γ := P ⊓ Subgroup.centralizer (K : Set Γ)
  let N' : Subgroup Γ := N ⊓ Y
  have hx₁P : x₁ ∈ P := by
    have h1 : (x₀ : Γ) * ((x₀ : Γ)⁻¹ * x₁) ∈ P := P.mul_mem x₀.2 (h.le hx₁coset)
    simpa using h1
  have hx₁C : x₁ ∈ Subgroup.centralizer (K : Set Γ) := by
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    exact mul_inv_eq_iff_eq_mul.mp (hx₁K k hk)
  have hx₁Y : x₁ ∈ Y := ⟨hx₁P, hx₁C⟩
  have heY : ∀ y ∈ Y, e * y * e⁻¹ ∈ Y := by
    rintro y ⟨hyP, hyC⟩
    refine ⟨h.norm_p e he y hyP, ?_⟩
    exact w172_conj_mem_centralizer (S := (K : Set Γ))
      (fun s hs => hFEA.comm heF hs.1)
      (fun s hs => hFEA.comm (F.inv_mem heF) hs.1) hyC
  have heN' : ∀ z ∈ N', e * z * e⁻¹ ∈ N' :=
    fun z hz => ⟨h.norm_n e he z hz.1, heY z hz.2⟩
  have hx₁normN' : x₁ ∈ Subgroup.normalizer (N' : Set Γ) := by
    rw [Subgroup.mem_normalizer_iff]
    intro z
    exact ⟨fun hz => ⟨(Subgroup.le_normalizer_iff.1 hPN) x₁ hx₁P z hz.1,
        Y.mul_mem (Y.mul_mem hx₁Y hz.2) (Y.inv_mem hx₁Y)⟩, fun hz => by
      refine ⟨?_, ?_⟩
      · have h1 : x₁⁻¹ * (x₁ * z * x₁⁻¹) * x₁ ∈ N := by
          simpa using (Subgroup.le_normalizer_iff.1 hPN) x₁⁻¹ (P.inv_mem hx₁P) _ hz.1
        rwa [show x₁⁻¹ * (x₁ * z * x₁⁻¹) * x₁ = z by group] at h1
      · have h1 : x₁⁻¹ * (x₁ * z * x₁⁻¹) * x₁ ∈ Y :=
          Y.mul_mem (Y.mul_mem (Y.inv_mem hx₁Y) hz.2) hx₁Y
        rwa [show x₁⁻¹ * (x₁ * z * x₁⁻¹) * x₁ = z by group] at h1⟩
  have henormN' : e ∈ Subgroup.normalizer (N' : Set Γ) := by
    rw [Subgroup.mem_normalizer_iff]
    intro z
    exact ⟨heN' z, fun hz => by
      have he2 : e * e = 1 := h.sq e he
      have he_inv : e⁻¹ = e := inv_eq_of_mul_eq_one_right he2
      have h1 : e * (e * z * e⁻¹) * e ∈ N' := by
        simpa [he_inv] using heN' (e * z * e⁻¹) hz
      rwa [show e * (e * z * e⁻¹) * e = z by
        calc e * (e * z * e⁻¹) * e = (e * e) * z * (e⁻¹ * e) := by group
          _ = z := by rw [he2, inv_mul_cancel]; simp] at h1⟩
  have hK'norm : (N' ⊔ Subgroup.zpowers x₁ ⊔ Subgroup.zpowers e) ≤
      Subgroup.normalizer (N' : Set Γ) :=
    sup_le (sup_le N'.le_normalizer (Subgroup.zpowers_le.2 hx₁normN'))
      (Subgroup.zpowers_le.2 henormN')
  have hx₁Q : ((⟨x₁, hx₁P⟩ : ↥P) : Q) = q := by
    have h : ((⟨x₁, hx₁P⟩ : ↥P) : Q) = ((x₀ : ↥P) : Q) := by
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
      simpa using N.inv_mem hx₁coset
    rw [h, hx₀Q]
  have hx₁_inv_N' : (e * x₁ * e⁻¹) * x₁ ∈ N' := by
    refine ⟨?_, Y.mul_mem (heY x₁ hx₁Y) hx₁Y⟩
    have hwP : ((⟨(e * x₁ * e⁻¹) * x₁,
        P.mul_mem (h.norm_p e he x₁ hx₁P) hx₁P⟩ : ↥P) : Q) = 1 := by
      have hmul : ((⟨(e * x₁ * e⁻¹) * x₁,
          P.mul_mem (h.norm_p e he x₁ hx₁P) hx₁P⟩ : ↥P) : Q) =
          ((⟨e * x₁ * e⁻¹, h.norm_p e he x₁ hx₁P⟩ : ↥P) : Q) *
            ((⟨x₁, hx₁P⟩ : ↥P) : Q) := by
        rw [← QuotientGroup.mk_mul]
        apply congrArg (fun z : ↥P => (z : Q))
        exact Subtype.ext rfl
      rw [hmul]
      have hmk : ((⟨e * x₁ * e⁻¹, h.norm_p e he x₁ hx₁P⟩ : ↥P) : Q) =
          Gf ⟨e, he⟩ ((⟨x₁, hx₁P⟩ : ↥P) : Q) := by
        rw [QuotientGroup.map_mk]
        apply congrArg (fun z : ↥P => (z : Q))
        exact Subtype.ext rfl
      rw [hmk, hx₁Q, hqinv, inv_mul_cancel]
    have h2 : (⟨(e * x₁ * e⁻¹) * x₁,
        P.mul_mem (h.norm_p e he x₁ hx₁P) hx₁P⟩ : ↥P) ∈ NP := by
      rw [QuotientGroup.eq_one_iff] at hwP
      exact hwP
    simpa using Subgroup.mem_subgroupOf.mp h2
  have hN'odd : Odd (Nat.card ↥N') :=
    hNodd.of_dvd_nat (Subgroup.card_dvd_of_le (inf_le_left : N' ≤ N))
  obtain ⟨u, -, hx₁uN', heu⟩ :=
    CFSG.GH74.GLS.C3.Layer1.Bk.exists_exact_inverted_lift_gen
      (K := N' ⊔ Subgroup.zpowers x₁ ⊔ Subgroup.zpowers e) (Y := N')
      (le_trans le_sup_left le_sup_left)
      (fun k hk y hy => (Subgroup.le_normalizer_iff.1 hK'norm) k hk y hy)
      hN'odd
      (Subgroup.mem_sup_right (Subgroup.mem_zpowers e))
      (Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.mem_zpowers x₁)))
      (by
        have he2 : e * e = 1 := h.sq e he
        calc e ^ 4 = e ^ 2 * e ^ 2 := by
              rw [show (4 : ℕ) = 2 + 2 by norm_num, pow_add]
          _ = (e * e) * (e * e) := by rw [pow_two]
          _ = 1 := by rw [he2, one_mul])
      hx₁_inv_N'
  have hx₁u_N : x₁⁻¹ * u ∈ N := (inf_le_left : N' ≤ N) hx₁uN'
  have huP : u ∈ P := by
    have h1 : x₁ * (x₁⁻¹ * u) ∈ P := P.mul_mem hx₁P (h.le hx₁u_N)
    simpa using h1
  have hx₀_notN : (x₀ : Γ) ∉ N := by
    intro hx₀N
    apply hq1
    rw [← hx₀Q, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    exact hx₀N
  have hx₁_notN : x₁ ∉ N := by
    intro hx₁N
    apply hx₀_notN
    rw [show (x₀ : Γ) = x₁ * ((x₀ : Γ)⁻¹ * x₁)⁻¹ by group]
    exact N.mul_mem hx₁N (N.inv_mem hx₁coset)
  have hu_notN : u ∉ N := by
    intro huN
    apply hx₁_notN
    rw [show x₁ = u * (x₁⁻¹ * u)⁻¹ by group]
    exact N.mul_mem huN (N.inv_mem hx₁u_N)
  have hu1 : u ≠ 1 := fun h1 => hu_notN (by rw [h1]; exact N.one_mem)
  have hKcen_u : ∀ k ∈ K, k * u * k⁻¹ = u := by
    intro k hk
    have hxk : k * x₁ = x₁ * k := (Subgroup.mem_centralizer_iff.1 hx₁C) k hk
    have hnk : k * (x₁⁻¹ * u) = (x₁⁻¹ * u) * k :=
      (Subgroup.mem_centralizer_iff.1 hx₁uN'.2.2) k hk
    calc k * u * k⁻¹ = k * (x₁ * (x₁⁻¹ * u)) * k⁻¹ := by rw [mul_inv_cancel_left]
      _ = (k * x₁ * k⁻¹) * (k * (x₁⁻¹ * u) * k⁻¹) := by group
      _ = x₁ * (x₁⁻¹ * u) := by rw [hxk, hnk]; group
      _ = u := mul_inv_cancel_left x₁ u
  have hfu_all : ∀ f ∈ D, f ≠ e → f * u * f⁻¹ = u := by
    intro f hf hfe
    rcases hw ⟨f, hf⟩ (Finset.mem_univ _) with hfix | hinv
    · exact hKcen_u f (hmemK_fix f hf hfix)
    · have hfK : e * f ∈ K := hmemK_inv f hf hinv
      have hefu : (e * f) * u * (e * f)⁻¹ = u := hKcen_u (e * f) hfK
      have hefcomm : e * f = f * e := h.comm e he f hf
      have h1 : e * (f * u * f⁻¹) * e⁻¹ = u := by
        have heq : (e * f) * u * (e * f)⁻¹ = e * (f * u * f⁻¹) * e⁻¹ := by
          group
        rwa [heq] at hefu
      have he2 : e * e = 1 := h.sq e he
      have he_inv : e⁻¹ = e := inv_eq_of_mul_eq_one_right he2
      have hfu_inv : f * u * f⁻¹ = u⁻¹ := by
        have h1' : f * u * f⁻¹ = e⁻¹ * u * e := by
          calc f * u * f⁻¹ = e⁻¹ * (e * (f * u * f⁻¹) * e⁻¹) * e := by group
            _ = e⁻¹ * u * e := by rw [h1]
        rw [h1', he_inv]
        rwa [he_inv] at heu
      exact absurd (h.no_two_inverted e he f hf (Ne.symm hfe) u huP heu hfu_inv) hu1
  obtain ⟨i, hi⟩ : ∃ i, orderOf u = p ^ i := by
    obtain ⟨i, hi⟩ := h.pgroup.exists_orderOf_eq_pow ⟨u, huP⟩
    exact ⟨i, (Subgroup.orderOf_coe ⟨u, huP⟩).trans hi⟩
  have hi_pos : 0 < i := by
    rcases i with _ | j
    · exfalso
      apply hu1
      rw [pow_zero] at hi
      exact orderOf_eq_one_iff.mp hi
    · exact Nat.succ_pos j
  have hp_dvd : p ∣ orderOf u := by
    rw [hi]
    exact dvd_pow_self p (Nat.pos_iff_ne_zero.mp hi_pos)
  let y : Γ := u ^ (orderOf u / p)
  have hyord : orderOf y = p :=
    orderOf_pow_orderOf_div (x := u) (n := p) (orderOf_pos u).ne' hp_dvd
  refine ⟨y, P.pow_mem huP _, ?_, ?_, ?_, ?_⟩
  · intro hy1
    rw [hy1, orderOf_one] at hyord
    exact h.prime.one_lt.ne hyord
  · rw [← hyord]; exact pow_orderOf_eq_one y
  · calc e * y * e⁻¹ = e * u ^ (orderOf u / p) * e⁻¹ := rfl
      _ = (e * u * e⁻¹) ^ (orderOf u / p) := (conj_pow).symm
      _ = (u⁻¹) ^ (orderOf u / p) := by rw [heu]
      _ = (u ^ (orderOf u / p))⁻¹ := by rw [inv_pow]
      _ = y⁻¹ := rfl
  · intro f hf hfe
    have hfu := hfu_all f hf hfe
    calc f * y * f⁻¹ = f * u ^ (orderOf u / p) * f⁻¹ := rfl
      _ = (f * u * f⁻¹) ^ (orderOf u / p) := (conj_pow).symm
      _ = u ^ (orderOf u / p) := by rw [hfu]
      _ = y := rfl

end CFSG.LocalAnalysis.WeakClosure81

end
