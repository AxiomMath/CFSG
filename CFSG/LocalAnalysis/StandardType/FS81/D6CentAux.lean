module

public import CFSG.LocalAnalysis.StandardType.FS81.StdLoc
public import CFSG.GroupTheory.IndexThreeCosets
public import CFSG.LocalAnalysis.StandardType.FS81.D6Inner
public import CFSG.LocalAnalysis.StandardType.FS81.SplitEAux

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open CFSG.Assembly

variable {G : Type} [Group G] {b₀ : G} {K E : Subgroup G}

theorem eq_one_of_commute_mul_pow_eq_one {H N : Subgroup G}
    (hcomm : ∀ h ∈ H, ∀ n ∈ N, h * n = n * h) (hdisj : H ⊓ N = ⊥)
    {h n : G} (hh : h ∈ H) (hn : n ∈ N) {m k : ℕ}
    (hmul : (h * n) ^ m = 1) (hk : h ^ k = 1) (hcop : Nat.Coprime m k) : h = 1 := by
  have hpow : h ^ m = 1 := by
    have hprod : h ^ m * n ^ m = 1 := by
      rw [← Commute.mul_pow (hcomm h hh n hn), hmul]
    have hmem : h ^ m ∈ H ⊓ N := by
      refine ⟨H.pow_mem hh m, ?_⟩
      rw [eq_inv_of_mul_eq_one_left hprod]
      exact N.inv_mem (N.pow_mem hn m)
    rw [hdisj] at hmem
    simpa using hmem
  have hdvd : orderOf h ∣ m := orderOf_dvd_of_pow_eq_one hpow
  have hdvd' : orderOf h ∣ k := orderOf_dvd_of_pow_eq_one hk
  have hg : orderOf h ∣ m.gcd k := Nat.dvd_gcd hdvd hdvd'
  rw [hcop] at hg
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hg)

theorem b₀_mem_inf_centralizer (hKC : K ≤ Subgroup.centralizer ({b₀} : Set G)) :
    b₀ ∈ Subgroup.centralizer ({b₀} : Set G) ⊓ Subgroup.centralizer (K : Set G) := by
  refine ⟨?_, ?_⟩
  · exact Subgroup.mem_centralizer_iff.mpr (fun y hy => by
      rw [Set.mem_singleton_iff] at hy
      rw [hy])
  · exact Subgroup.mem_centralizer_iff.mpr (fun k hk =>
      (Subgroup.mem_centralizer_iff.mp (hKC hk) b₀ (by simp)).symm)

private theorem d6_inf_centralizer_inf_eq_bot (hKC : K ≤ Subgroup.centralizer ({b₀} : Set G))
    (hKz : Subgroup.center K = ⊥) :
    (Subgroup.centralizer ({b₀} : Set G) ⊓ Subgroup.centralizer (K : Set G)) ⊓ K = ⊥ := by
  rw [eq_bot_iff]
  intro a ha
  have haK : a ∈ K := ha.2
  have haCK : a ∈ Subgroup.centralizer (K : Set G) := ha.1.2
  have hcenter : (⟨a, haK⟩ : K) ∈ Subgroup.center K := by
    rw [Subgroup.mem_center_iff]
    intro b
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp haCK (b : K) b.2
  rw [hKz] at hcenter
  simpa using hcenter

theorem commute_zpowers_sup_K_of_le_inf {R : Subgroup G}
    (hRZ : R ≤ Subgroup.centralizer ({b₀} : Set G) ⊓
      Subgroup.centralizer (K : Set G)) :
    ∀ r ∈ R, ∀ t ∈ Subgroup.zpowers b₀ ⊔ K, r * t = t * r := by
  intro r hr t ht
  have hb₀c : b₀ ∈ Subgroup.centralizer ({r} : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    rw [hx]
    exact (Subgroup.mem_centralizer_iff.mp (hRZ hr).1 b₀ (by simp)).symm
  have hKc : K ≤ Subgroup.centralizer ({r} : Set G) := by
    intro k hk
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    rw [hx]
    exact (Subgroup.mem_centralizer_iff.mp (hRZ hr).2 k hk).symm
  have hTc : Subgroup.zpowers b₀ ⊔ K ≤ Subgroup.centralizer ({r} : Set G) :=
    sup_le (Subgroup.zpowers_le.mpr hb₀c) hKc
  exact Subgroup.mem_centralizer_iff.mp (hTc ht) r (by simp)

private theorem d6Cube {G : Type} [Group G] [Finite G] {b₀ : G} {K E : Subgroup G}
    (hstd : StdLoc b₀ K E Row.D6) {B : Basis3 G (Row.D6.n + 1)} (hB : Adapted B b₀ K E)
    (hrec : RecOut Row.D6 B b₀) {w n : G}
    (hwZ : w ∈ Subgroup.centralizer ({b₀} : Set G) ⊓ Subgroup.centralizer (K : Set G))
    (hw3 : w ^ 3 = b₀) (hn : n ∈ Subgroup.normalizer (E : Set G)) :
    n * b₀ * n⁻¹ ∈ Subgroup.zpowers b₀ := by
  obtain ⟨hA, hE, hb₀E, -, -, -⟩ := hstd.2.1
  obtain ⟨hb₀ord, hKC, hKn, hKz, -, hA2, -, -⟩ := hA
  obtain ⟨hrow, hdisj, hsupE, hmaxA, hcardA, hCK⟩ := hstd.2.2
  have hspan : B.span = E := hB.1
  obtain ⟨hEC, hEel, hEmax⟩ := hE
  obtain ⟨hAK, hAel, hAmax⟩ := hmaxA
  have hb₀Z : b₀ ∈ Subgroup.centralizer ({b₀} : Set G) ⊓
      Subgroup.centralizer (K : Set G) := b₀_mem_inf_centralizer hKC
  have hZK : (Subgroup.centralizer ({b₀} : Set G) ⊓
      Subgroup.centralizer (K : Set G)) ⊓ K = ⊥ := d6_inf_centralizer_inf_eq_bot hKC hKz
  have hwE : ∀ e ∈ E, w * e = e * w := by
    intro e he
    have hEcent : E ≤ Subgroup.centralizer ({w} : Set G) := by
      rw [← hsupE]
      refine sup_le (Subgroup.zpowers_le.mpr ?_) ?_
      · rw [Subgroup.mem_centralizer_iff]
        intro x hx
        rw [Set.mem_singleton_iff] at hx
        rw [hx]
        exact (Subgroup.mem_centralizer_iff.mp hwZ.1 b₀ (by simp)).symm
      · intro a ha
        rw [Subgroup.mem_centralizer_iff]
        intro x hx
        rw [Set.mem_singleton_iff] at hx
        rw [hx]
        exact (Subgroup.mem_centralizer_iff.mp hwZ.2 a ha.2).symm
    exact Subgroup.mem_centralizer_iff.mp (hEcent he) w (by simp)
  let y := n * w * n⁻¹
  have hyE : y ∈ Subgroup.centralizer (E : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    have hne : n⁻¹ * e * n ∈ E := by
      simpa using (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hn) e).mp he
    have h1 : y * e * y⁻¹ = e := by
      have hstep : y * e * y⁻¹ = n * (w * (n⁻¹ * e * n) * w⁻¹) * n⁻¹ := by
        show n * w * n⁻¹ * e * (n * w * n⁻¹)⁻¹ = _
        group
      rw [hstep, hwE (n⁻¹ * e * n) hne]
      group
    have h2 : y * e = e * y := by
      have := congrArg (· * y) h1
      simpa [mul_assoc] using this
    exact h2.symm
  have hyC : y ∈ Subgroup.centralizer ({b₀} : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    rw [hx]
    exact Subgroup.mem_centralizer_iff.mp hyE b₀ hb₀E
  obtain ⟨k, hkK, hk⟩ := exists_inner_D6 hstd hB hrec hyC
  let z := k⁻¹ * y
  have hkC : k ∈ Subgroup.centralizer ({b₀} : Set G) := hKC hkK
  have hzC : z ∈ Subgroup.centralizer ({b₀} : Set G) :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ hkC) hyC
  have hzK : z ∈ Subgroup.centralizer (K : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    have h1 : z * a * z⁻¹ = a := by
      have hstep : z * a * z⁻¹ = k⁻¹ * (y * a * y⁻¹) * k := by
        show k⁻¹ * y * a * (k⁻¹ * y)⁻¹ = _
        group
      rw [hstep]
      simpa [mul_assoc] using congrArg (fun t => k⁻¹ * t * k) (hk a ha)
    have h2 : z * a = a * z := by
      have := congrArg (· * z) h1
      simpa [mul_assoc] using this
    exact h2.symm
  have hzZ : z ∈ Subgroup.centralizer ({b₀} : Set G) ⊓
      Subgroup.centralizer (K : Set G) := ⟨hzC, hzK⟩
  have hkA : k ∈ E ⊓ K := by
    rw [← hCK]
    refine ⟨?_, hkK⟩
    refine Subgroup.mem_centralizer_iff.mpr ?_
    intro a ha
    have h1 : y * a * y⁻¹ = a := by
      have hcomm := Subgroup.mem_centralizer_iff.mp hyE a ha.1
      have := congrArg (· * y⁻¹) hcomm
      simpa [mul_assoc] using this.symm
    have h2 : y * a * y⁻¹ = k * a * k⁻¹ := hk a ha.2
    rw [h1] at h2
    have := congrArg (· * k) h2
    simpa [mul_assoc] using this
  have hk3 : k ^ 3 = 1 := hAel.2 k hkA
  have hkz : Commute k z := Subgroup.mem_centralizer_iff.mp hzK k hkK
  have hykz : y = k * z := by simp [z]
  have hcube : n * b₀ * n⁻¹ = z ^ 3 := by
    have hy3 : y ^ 3 = n * b₀ * n⁻¹ := by
      show (n * w * n⁻¹) ^ 3 = n * b₀ * n⁻¹
      rw [conj_pow, hw3]
    calc n * b₀ * n⁻¹ = y ^ 3 := hy3.symm
      _ = z ^ 3 := by rw [hykz, hkz.mul_pow, hk3, one_mul]
  have hmemE : n * b₀ * n⁻¹ ∈ E := (Subgroup.mem_normalizer_iff.mp hn b₀).mp hb₀E
  have hmemZ : n * b₀ * n⁻¹ ∈ Subgroup.centralizer ({b₀} : Set G) ⊓
      Subgroup.centralizer (K : Set G) := by
    rw [hcube]
    exact ⟨Subgroup.pow_mem _ hzC 3, Subgroup.pow_mem _ hzK 3⟩
  have hcomm : ∀ a ∈ Subgroup.zpowers b₀, ∀ b ∈ E ⊓ K, a * b = b * a := by
    intro a ha b hb
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp ha
    rw [← hi]
    exact (show Commute b₀ b from hEel.comm hb₀E hb.1).zpow_left i
  have hEZ : E ⊓ (Subgroup.centralizer ({b₀} : Set G) ⊓
      Subgroup.centralizer (K : Set G)) ≤ Subgroup.zpowers b₀ := by
    intro x hx
    have hxE : x ∈ E := hx.1
    have hxZ : x ∈ Subgroup.centralizer ({b₀} : Set G) ⊓
        Subgroup.centralizer (K : Set G) := hx.2
    rw [← hsupE] at hxE
    obtain ⟨r, hr, a, ha, hxra⟩ := fs81Sp_mem_sup_of_commute hcomm hxE
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hr
    have hrZ : r ∈ Subgroup.centralizer ({b₀} : Set G) ⊓
        Subgroup.centralizer (K : Set G) := by
      rw [← hi]
      exact ⟨(Subgroup.centralizer ({b₀} : Set G)).zpow_mem hb₀Z.1 i,
        (Subgroup.centralizer (K : Set G)).zpow_mem hb₀Z.2 i⟩
    have haZ : a ∈ Subgroup.centralizer ({b₀} : Set G) ⊓
        Subgroup.centralizer (K : Set G) := by
      have haeq : a = r⁻¹ * x := by rw [hxra]; group
      rw [haeq]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hrZ) hxZ
    have hbot : a ∈ (⊥ : Subgroup G) := by
      rw [← hZK]
      exact ⟨haZ, ha.2⟩
    have ha1 : a = 1 := by simpa using hbot
    rw [hxra, ha1, mul_one]
    exact hr
  exact hEZ ⟨hmemE, hmemZ⟩

private theorem d6Card {G : Type} [Group G] [Finite G] {b₀ : G} {K E : Subgroup G}
    (hstd : StdLoc b₀ K E Row.D6) {B : Basis3 G (Row.D6.n + 1)} (hB : Adapted B b₀ K E)
    (hrec : RecOut Row.D6 B b₀)
    (hN : ∀ n ∈ Subgroup.normalizer (E : Set G), n * b₀ * n⁻¹ ∈ Subgroup.zpowers b₀) :
    Nat.card ↥(B.realized ⊤) ≤
      2 * Nat.card ↥(B.realized (Subgroup.centralizer ({b₀} : Set G))) := by
  obtain ⟨hA, hE, hb₀E, -, -, -⟩ := hstd.2.1
  obtain ⟨hb₀ord, hKC, hKn, hKz, -, hA2, -, -⟩ := hA
  let C := Subgroup.centralizer ({b₀} : Set G)
  change Nat.card ↥(B.realized ⊤) ≤ 2 * Nat.card ↥(B.realized C)
  have hspan : B.span = E := hB.1
  have hN' : ∀ g ∈ Subgroup.normalizer (B.span : Set G), g * b₀ * g⁻¹ ∈ Subgroup.zpowers b₀ := by
    intro g hg
    exact hN g (by simpa [hspan] using hg)
  have hx_ne : ∀ g ∈ Subgroup.normalizer (B.span : Set G), g * b₀ * g⁻¹ ≠ 1 := by
    intro g hg h1
    have hord : orderOf (g * b₀ * g⁻¹) = 3 := by
      rw [show g * b₀ * g⁻¹ = (MulAut.conj g) b₀ by rw [MulAut.conj_apply]]
      exact (MulEquiv.orderOf_eq (MulAut.conj g) b₀).trans hb₀ord
    rw [h1, orderOf_one] at hord
    norm_num at hord
  have hcase : ∀ g ∈ Subgroup.normalizer (B.span : Set G),
      g * b₀ * g⁻¹ = b₀ ∨ g * b₀ * g⁻¹ = b₀⁻¹ :=
    fun g hg => CFSG.GroupTheory.eq_or_eq_inv_of_mem_zpowers_of_orderOf_eq_three
      hb₀ord (hN' g hg) (hx_ne g hg)
  have hmemC : ∀ {g : G}, g * b₀ * g⁻¹ = b₀ → g ∈ C := by
    intro g hg
    exact Subgroup.mem_centralizer_iff.mpr (fun x hx => by
      rw [Set.mem_singleton_iff] at hx
      rw [hx]
      have h := congrArg (· * g) hg
      simpa [mul_assoc] using h.symm)
  by_cases hex : ∃ g ∈ Subgroup.normalizer (B.span : Set G), g * b₀ * g⁻¹ ≠ b₀
  · obtain ⟨g₁, hg₁, hne₁⟩ := hex
    obtain ⟨M₁, hM₁⟩ := Basis3.exists_acts B hg₁
    have hg₁_c : g₁ * b₀ * g₁⁻¹ = b₀⁻¹ := (hcase g₁ hg₁).resolve_left hne₁
    have hsub : B.realized ⊤ ⊆
        B.realized C ∪ (fun M' => M₁ * M') '' B.realized C := by
      rintro A ⟨g, -, hActs⟩
      have hgN : g ∈ Subgroup.normalizer (B.span : Set G) := Basis3.mem_normalizer_of_acts B hActs
      rcases hcase g hgN with hgb | hgb
      · exact Or.inl ⟨g, hmemC hgb, hActs⟩
      · right
        have hhN : g₁⁻¹ * g ∈ Subgroup.normalizer (B.span : Set G) :=
          Subgroup.mul_mem _ (Subgroup.inv_mem _ hg₁) hgN
        have hhC : g₁⁻¹ * g ∈ C := by
          apply hmemC
          have hstep : (g₁⁻¹ * g) * b₀ * (g₁⁻¹ * g)⁻¹ =
              g₁⁻¹ * (g * b₀ * g⁻¹) * g₁ := by
            group
          rw [hstep, hgb, ← hg₁_c]
          group
        obtain ⟨M', hM'⟩ := Basis3.exists_acts B hhN
        refine ⟨M', ⟨g₁⁻¹ * g, hhC, hM'⟩, ?_⟩
        have hmul : B.Acts g (M₁ * M') := by
          have h := Basis3.acts_mul B hM₁ hM'
          rwa [show g₁ * (g₁⁻¹ * g) = g by group] at h
        exact (Basis3.acts_unique B hActs hmul).symm
    calc Nat.card ↥(B.realized ⊤) = (B.realized ⊤).ncard := Nat.card_coe_set_eq _
      _ ≤ (B.realized C ∪ (fun M' => M₁ * M') '' B.realized C).ncard :=
          Set.ncard_le_ncard hsub
      _ ≤ (B.realized C).ncard + ((fun M' => M₁ * M') '' B.realized C).ncard :=
          Set.ncard_union_le _ _
      _ ≤ (B.realized C).ncard + (B.realized C).ncard :=
          Nat.add_le_add_left (Set.ncard_image_le (s := B.realized C)) _
      _ = Nat.card ↥(B.realized C) + Nat.card ↥(B.realized C) := rfl
      _ = 2 * Nat.card ↥(B.realized C) := by ring
  · have hsub : B.realized ⊤ ⊆ B.realized C := by
      rintro A ⟨g, -, hActs⟩
      have hgN : g ∈ Subgroup.normalizer (B.span : Set G) := Basis3.mem_normalizer_of_acts B hActs
      have hgb : g * b₀ * g⁻¹ = b₀ := by
        by_contra hne
        exact hex ⟨g, hgN, hne⟩
      exact ⟨g, hmemC hgb, hActs⟩
    have h1 : Nat.card ↥(B.realized ⊤) ≤ Nat.card ↥(B.realized C) := by
      calc Nat.card ↥(B.realized ⊤) = (B.realized ⊤).ncard := Nat.card_coe_set_eq _
        _ ≤ (B.realized C).ncard := Set.ncard_le_ncard hsub
        _ = Nat.card ↥(B.realized C) := Nat.card_coe_set_eq _
    omega

theorem d6NoCube {G : Type} [Group G] [Finite G] {b₀ : G} {K E : Subgroup G}
    (hstd : StdLoc b₀ K E Row.D6) {B : Basis3 G (Row.D6.n + 1)} (hB : Adapted B b₀ K E)
    (hrec : RecOut Row.D6 B b₀) :
    ¬ ∃ w : G, w ∈ Subgroup.centralizer ({b₀} : Set G) ⊓
      Subgroup.centralizer (K : Set G) ∧ w ^ 3 = b₀ := by
  rintro ⟨w, hwZ, hw3⟩
  have hN : ∀ n ∈ Subgroup.normalizer (E : Set G), n * b₀ * n⁻¹ ∈ Subgroup.zpowers b₀ :=
    fun n hn => d6Cube hstd hB hrec hwZ hw3 hn
  have hcard := d6Card hstd hB hrec hN
  have hrealC : Nat.card ↥(B.realized (Subgroup.centralizer ({b₀} : Set G))) ≤
      2 ^ 7 * Nat.factorial 7 := by
    have hsub := realized_centralizer_subset_evenFix0_D6 hstd hB hrec
    calc Nat.card ↥(B.realized (Subgroup.centralizer ({b₀} : Set G)))
        = (B.realized (Subgroup.centralizer ({b₀} : Set G))).ncard := Nat.card_coe_set_eq _
      _ ≤ (evenFix0 Row.D6.n).ncard := Set.ncard_le_ncard hsub
      _ = Nat.card ↥(evenFix0 Row.D6.n) := (Nat.card_coe_set_eq _).symm
      _ ≤ 2 ^ 7 * Nat.factorial 7 := card_spSet_le 7 _
  have hmono := Basis3.card_ggAutomizer_le B ⊤
  have hrec1 : Nat.card ↥(ggAutomizer ⊤ B.span) = 2903040 := hrec.1
  have hchain : 2903040 ≤ 2 * (2 ^ 7 * Nat.factorial 7) := by
    calc 2903040 = Nat.card ↥(ggAutomizer ⊤ B.span) := hrec1.symm
      _ ≤ Nat.card ↥(B.realized ⊤) := hmono
      _ ≤ 2 * Nat.card ↥(B.realized (Subgroup.centralizer ({b₀} : Set G))) := hcard
      _ ≤ 2 * (2 ^ 7 * Nat.factorial 7) := Nat.mul_le_mul_left 2 hrealC
  have hlt : 2 * (2 ^ 7 * Nat.factorial 7) < 2903040 := by norm_num
  omega

end CFSG.StandardType.FrameRoute.FS81
