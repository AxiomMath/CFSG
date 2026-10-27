module

public import CFSG.LocalAnalysis.StandardType.GGQ2OrthTorusConj
public import CFSG.LocalAnalysis.StandardType.GGQ2OrthStatements
import CFSG.LocalAnalysis.StandardType.GGQ2SpBlocksCentExt
import CFSG.LocalAnalysis.StandardType.GGQ2CentInternal
import CFSG.GroupTheory.CenterlessInnerCentralizer
import CFSG.LocalAnalysis.StandardType.GGQ2OrthTorusAutBasic
import CFSG.GroupTheory.PCore.SubgroupCore

public section

namespace CFSG.StandardType.GGQ2Frame.OrthPlacement

open CFSG CFSG.Assembly CFSG.StandardType Matrix
open CFSG.Open (IsElemAbelian)
open CFSG.StandardType.GGQ2Frame.OrthBlocks

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

noncomputable section

private theorem oef_liftV_injective (t : ℕ) (δ : Fin 2) :
    Function.Injective (liftV t δ) := by
  intro u v h
  funext i
  have h' := congrFun h (Fin.castAdd δ.val i)
  simpa [liftV, Fin.append] using h'

private theorem oef_omegaQ_conj_mem {K : Type} [Field K] (t : ℕ) (δ : Fin 2)
    {P x : GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K}
    (hP : P ∈ LargeEvenOrthGroup (planeQ (K := K) t δ))
    (hx : x ∈ omegaQ (K := K) t δ) :
    MulAut.conj P x ∈ omegaQ (K := K) t δ := by
  have hO : (LargeEvenOrthGroup (planeQ (K := K) t δ)).map
      (MulAut.conj P).toMonoidHom = LargeEvenOrthGroup (planeQ (K := K) t δ) := by
    apply le_antisymm
    · rintro _ ⟨y, hy, rfl⟩
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hP hy) (Subgroup.inv_mem _ hP)
    · intro y hy
      refine ⟨P⁻¹ * y * P, ?_, ?_⟩
      · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hP) hy) hP
      · change P * (P⁻¹ * y * P) * P⁻¹ = y
        group
  rw [omegaQ, largeEvenOmega_def] at hx ⊢
  have hmem : (MulAut.conj P) x ∈
      (⁅LargeEvenOrthGroup (planeQ (K := K) t δ),
        LargeEvenOrthGroup (planeQ (K := K) t δ)⁆).map
          (MulAut.conj P).toMonoidHom :=
    Subgroup.mem_map_of_mem _ hx
  rwa [Subgroup.map_commutator, hO] at hmem

private theorem oef_exists_pow_three_eq_one_of_ker {H R : Type*} [Group H] [Finite H] [Group R]
    (π : H →* R) (hπ : Function.Surjective π) (hker : π.ker = Subgroup.center H)
    (hZ : ¬ 3 ∣ Nat.card ↥(Subgroup.center H)) {g : R} (hg : g ^ 3 = 1) :
    ∃ x : H, x ^ 3 = 1 ∧ π x = g := by
  obtain ⟨x₀, rfl⟩ := hπ g
  let y : H := x₀ ^ 3
  have hy_center : y ∈ Subgroup.center H := by
    have hy_ker : y ∈ π.ker := by
      rw [MonoidHom.mem_ker]
      change π (x₀ ^ 3) = 1
      rw [map_pow, hg]
    rwa [hker] at hy_ker
  have hcop : Nat.Coprime (Nat.card ↥(Subgroup.center H)) 3 :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hZ |>.symm
  obtain ⟨z, hz3⟩ := (Nat.Coprime.pow_left_bijective hcop).surjective
    (⟨y⁻¹, Subgroup.inv_mem _ hy_center⟩ : ↥(Subgroup.center H))
  refine ⟨x₀ * (z : H), ?_, ?_⟩
  · have hcomm : Commute x₀ (z : H) :=
      Subgroup.mem_center_iff.mp z.2 x₀
    calc (x₀ * (z : H)) ^ 3 = x₀ ^ 3 * (z : H) ^ 3 := hcomm.mul_pow 3
      _ = y * (z : H) ^ 3 := rfl
      _ = y * y⁻¹ := by rw [show (z : H) ^ 3 = y⁻¹ from congrArg Subtype.val hz3]
      _ = 1 := mul_inv_cancel y
  · have hzker : (z : H) ∈ π.ker := by
      rw [hker]
      exact z.2
    rw [map_mul, MonoidHom.mem_ker.mp hzker, mul_one]

theorem existsOrthFrame_of_torusConj (hT : OrthTorusConj) : ExistsOrthFrame := by
  intro G _ _ H E t δ K _ _ _ θ hK hperf hE h4 hEN hI hSC hdisc hZ h33
  classical
  let Ω : Subgroup (GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) := omegaQ (K := K) t δ
  have hπ₀ker : (ggQuotHom θ).ker = Subgroup.center ↥H := ker_ggQuotHom θ
  have hπ₀surj : Function.Surjective (ggQuotHom θ) := ggQuotHom_surjective θ
  have hZcent : Subgroup.center ↥(omegaQ (K := K) t δ) = ⊥ :=
    GGQ2CentPort.ggQ2Cent_center_eq_bot hperf θ
  have hconjinj : Function.Injective (MulAut.conj : ↥(omegaQ (K := K) t δ) →*
      MulAut ↥(omegaQ (K := K) t δ)) :=
    CFSG.mulAutConj_injective_of_center_eq_bot hZcent
  have hmem : ∀ b : ↥E, ∃ a : ↥Ω, MulAut.conj a = ggLAut H θ ⟨b, hEN b.2⟩ := by
    intro b
    exact hI b b.2
  let aOf : ↥E → ↥Ω := fun b => Classical.choose (hmem b)
  have haOf : ∀ b : ↥E, MulAut.conj (aOf b) = ggLAut H θ ⟨b, hEN b.2⟩ :=
    fun b => Classical.choose_spec (hmem b)
  let ρ : ↥E →* ↥Ω :=
    { toFun := aOf
      map_one' := by
        apply hconjinj
        rw [haOf 1]
        change ggLAut H θ (1 : Subgroup.normalizer (H : Set G)) =
          MulAut.conj (1 : ↥Ω)
        simp
      map_mul' := by
        intro b c
        apply hconjinj
        calc MulAut.conj (aOf (b * c)) = ggLAut H θ ⟨b * c, hEN (b * c).2⟩ := haOf (b * c)
          _ = ggLAut H θ (⟨b, hEN b.2⟩ * ⟨c, hEN c.2⟩) := rfl
          _ = ggLAut H θ ⟨b, hEN b.2⟩ * ggLAut H θ ⟨c, hEN c.2⟩ :=
              map_mul (ggLAut H θ) _ _
          _ = MulAut.conj (aOf b) * MulAut.conj (aOf c) := by rw [haOf b, haOf c]
          _ = MulAut.conj (aOf b * aOf c) := (map_mul _ _ _).symm }
  have hρinj : Function.Injective ρ := by
    intro b c hbc
    have hd : ρ (b * c⁻¹) = 1 := by
      rw [map_mul, map_inv, hbc, mul_inv_cancel]
    have hLA : ggLAut H θ ⟨((b * c⁻¹ : ↥E) : G), hEN (b * c⁻¹).2⟩ = 1 := by
      have h := haOf (b * c⁻¹)
      rw [show aOf (b * c⁻¹) = ρ (b * c⁻¹) from rfl, hd, map_one] at h
      exact h.symm
    have hcent : (((b * c⁻¹ : ↥E) : G)) ∈ Subgroup.centralizer (H : Set G) :=
      mem_centralizer_of_ggLAut_eq_one H θ hperf hLA
    have hmem' : (((b * c⁻¹ : ↥E) : G)) ∈ E ⊓ Subgroup.centralizer (H : Set G) :=
      ⟨(b * c⁻¹).2, hcent⟩
    rw [hdisc] at hmem'
    have hbc1 : b * c⁻¹ = 1 := Subtype.ext (Subgroup.mem_bot.mp hmem')
    calc b = b * c⁻¹ * c := by group
      _ = c := by rw [hbc1, one_mul]
  have hρ : ∀ (b : ↥E) (h : ↥H),
      ggQuotHom θ (H.normalizerMonoidHom ⟨(b : G), hEN b.2⟩ h) =
        ρ b * ggQuotHom θ h * (ρ b)⁻¹ := by
    intro b h
    have h1 : ggQuotHom θ (H.normalizerMonoidHom ⟨(b : G), hEN b.2⟩ h) =
        ggLAut H θ ⟨(b : G), hEN b.2⟩ (ggQuotHom θ h) :=
      (ggBeta_ggQuotHom H hEN θ b h).symm
    calc ggQuotHom θ (H.normalizerMonoidHom ⟨(b : G), hEN b.2⟩ h)
        = ggLAut H θ ⟨(b : G), hEN b.2⟩ (ggQuotHom θ h) := h1
      _ = MulAut.conj (ρ b) (ggQuotHom θ h) := by
          simpa [ρ] using congrArg (fun f : MulAut ↥Ω => f (ggQuotHom θ h)) (haOf b).symm
      _ = ρ b * ggQuotHom θ h * (ρ b)⁻¹ := by rw [MulAut.conj_apply]
  let A : Subgroup ↥Ω := ρ.range
  have hAab : IsElemAbelian 3 A := by
    constructor
    · refine IsMulCommutative.of_comm ?_
      rintro ⟨x, hx⟩ ⟨y, hy⟩
      obtain ⟨a, rfl⟩ := hx
      obtain ⟨b, rfl⟩ := hy
      apply Subtype.ext
      calc (ρ a) * (ρ b) = ρ (a * b) := (map_mul ρ a b).symm
        _ = ρ (b * a) := by rw [hE.1.is_comm.comm a b]
        _ = ρ b * ρ a := map_mul ρ b a
    · intro x hx
      rw [MonoidHom.mem_range] at hx
      obtain ⟨a, rfl⟩ := hx
      have ha : a ^ 3 = 1 := by
        apply Subtype.ext
        simpa using hE.2 (a : G) a.2
      have hρa : (ρ a) ^ 3 = 1 := by rw [← map_pow, ha, map_one]
      apply Subtype.ext
      change ((ρ a : ↥Ω) : GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) ^ 3 = 1
      rw [← Subgroup.coe_pow, hρa]
      rfl
  have hZ3 : ¬ 3 ∣ Nat.card ↥(Subgroup.center ↥H) := by
    have hle : (Subgroup.center ↥H).map H.subtype ≤ Subgroup.centralizer (H : Set G) := by
      rintro z hz
      rw [Subgroup.mem_map] at hz
      obtain ⟨y, hy, rfl⟩ := hz
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hy ⟨h, hh⟩)
    intro h3
    have h3map : 3 ∣ Nat.card ↥((Subgroup.center ↥H).map H.subtype) := by
      rwa [Subgroup.card_map_of_injective H.subtype_injective]
    exact hZ (h3map.trans (Subgroup.card_dvd_of_le hle))
  have hAsc : ∀ g : ↥Ω, (∀ a ∈ A, g * a = a * g) → g ^ 3 = 1 → g ∈ A := by
    intro g hgcomm hg3
    obtain ⟨x, hx3, hπx⟩ :=
      oef_exists_pow_three_eq_one_of_ker (ggQuotHom θ) hπ₀surj hπ₀ker hZ3 hg3
    have hx3G : (x : G) ^ 3 = 1 := by
      simpa using congrArg Subtype.val hx3
    have hxE : (x : G) ∈ E := by
      apply hSC (x : G) ?_ hx3G
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      let bn : Subgroup.normalizer (H : Set G) := ⟨b, hEN hb⟩
      have h1 : ggQuotHom θ (H.normalizerMonoidHom bn x) =
          ρ ⟨b, hb⟩ * ggQuotHom θ x * (ρ ⟨b, hb⟩)⁻¹ := by
        simpa [bn] using hρ ⟨b, hb⟩ x
      have h2 : ρ ⟨b, hb⟩ ∈ A := ⟨⟨b, hb⟩, rfl⟩
      have h3 : ρ ⟨b, hb⟩ * g = g * ρ ⟨b, hb⟩ := (hgcomm _ h2).symm
      have h4 : ggQuotHom θ (H.normalizerMonoidHom bn x) = g := by
        rw [h1, hπx, h3]
        group
      let w : ↥H := x⁻¹ * H.normalizerMonoidHom bn x
      have hw_center : w ∈ Subgroup.center ↥H := by
        have hwker : w ∈ (ggQuotHom θ).ker := by
          rw [MonoidHom.mem_ker]
          change ggQuotHom θ (x⁻¹ * H.normalizerMonoidHom bn x) = 1
          rw [map_mul, map_inv, hπx, h4, inv_mul_cancel]
        rwa [hπ₀ker] at hwker
      have hw3 : w ^ 3 = 1 := by
        have hy3 : (H.normalizerMonoidHom bn x) ^ 3 = 1 := by
          have h : H.normalizerMonoidHom bn (x ^ 3) = 1 := by rw [hx3, map_one]
          simpa using h
        have hxw : H.normalizerMonoidHom bn x = x * w := by
          change H.normalizerMonoidHom bn x = x * (x⁻¹ * H.normalizerMonoidHom bn x)
          group
        rw [hxw] at hy3
        have hcommxw : Commute x w := Subgroup.mem_center_iff.mp hw_center x
        rw [hcommxw.mul_pow 3, hx3, one_mul] at hy3
        exact hy3
      have hw1 : w = 1 := by
        have hdvd3 : orderOf w ∣ 3 := orderOf_dvd_of_pow_eq_one hw3
        have hdvdcard : orderOf w ∣ Nat.card ↥(Subgroup.center ↥H) :=
          Subgroup.orderOf_dvd_natCard (Subgroup.center ↥H) hw_center
        have hcop : Nat.Coprime (Nat.card ↥(Subgroup.center ↥H)) 3 :=
          (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hZ3 |>.symm
        exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop hdvdcard hdvd3)
      have hyx : H.normalizerMonoidHom bn x = x := by
        have hxw : H.normalizerMonoidHom bn x = x * w := by
          change H.normalizerMonoidHom bn x = x * (x⁻¹ * H.normalizerMonoidHom bn x)
          group
        rw [hxw, hw1, mul_one]
      have hcoe : b * (x : G) * b⁻¹ = (x : G) := by
        have := congrArg Subtype.val hyx
        rwa [Subgroup.normalizerMonoidHom_apply_apply_coe] at this
      calc b * (x : G) = (b * (x : G) * b⁻¹) * b := by group
        _ = (x : G) * b := by rw [hcoe]
    have hρx : ρ ⟨(x : G), hxE⟩ = ggQuotHom θ x := by
      apply hconjinj
      rw [show ρ ⟨(x : G), hxE⟩ = aOf ⟨(x : G), hxE⟩ from rfl, haOf ⟨(x : G), hxE⟩]
      have hconj_eq : MulAut.conj (ggQuotHom θ x) =
          ggLAut H θ ⟨(x : G), hEN hxE⟩ := by
        apply MulEquiv.ext
        intro y
        obtain ⟨q, rfl⟩ := θ.surjective y
        induction q using QuotientGroup.induction_on with
        | H h =>
          rw [MulAut.conj_apply, ggLAut_apply]
          change ggQuotHom θ x * θ (h : ↥H ⧸ Subgroup.center ↥H) * (ggQuotHom θ x)⁻¹ =
            θ ((H.normalizerMonoidHom ⟨(x : G), hEN hxE⟩ h : ↥H) :
              ↥H ⧸ Subgroup.center ↥H)
          rw [← ggQuotHom_apply]
          calc ggQuotHom θ x * ggQuotHom θ h * (ggQuotHom θ x)⁻¹
              = ggQuotHom θ (x * h * x⁻¹) := by rw [← map_mul, ← map_inv, ← map_mul]
            _ = ggQuotHom θ (H.normalizerMonoidHom ⟨(x : G), hEN hxE⟩ h) := rfl
            _ = θ ((H.normalizerMonoidHom ⟨(x : G), hEN hxE⟩ h : ↥H) :
                ↥H ⧸ Subgroup.center ↥H) := ggQuotHom_apply θ _
      exact hconj_eq.symm
    have hgA : g ∈ A := by
      rw [← hπx, ← hρx]
      exact ⟨⟨(x : G), hxE⟩, rfl⟩
    exact hgA
  obtain ⟨ζ, P, hζinj, hisom, hconj⟩ :=
    hT (K := K) t δ hK h4 A hAab hAsc
  have hP : P ∈ LargeEvenOrthGroup (planeQ (K := K) t δ) := by
    rw [largeEvenOrthGroup_def]
    exact Subgroup.subset_closure hisom
  have hΩmap : Ω.map (MulAut.conj P).toMonoidHom = Ω := by
    change (omegaQ (K := K) t δ).map (MulAut.conj P).toMonoidHom = omegaQ (K := K) t δ
    apply le_antisymm
    · rintro _ ⟨y, hy, rfl⟩
      exact oef_omegaQ_conj_mem t δ hP hy
    · intro y hy
      refine ⟨MulAut.conj P⁻¹ y, ?_, ?_⟩
      · exact oef_omegaQ_conj_mem t δ (Subgroup.inv_mem _ hP) hy
      · change P * (P⁻¹ * y * P) * P⁻¹ = y
        group
  let cP : ↥Ω ≃* ↥Ω :=
    (Subgroup.equivMapOfInjective Ω (MulAut.conj P).toMonoidHom
      (MulAut.conj P).injective).trans (MulEquiv.subgroupCongr hΩmap)
  have hcP : ∀ x : ↥Ω, ((cP x : ↥Ω) :
      GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) =
      P * ((x : ↥Ω) : GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) * P⁻¹ := by
    intro x
    rfl
  let π : ↥H →* ↥Ω := cP.toMonoidHom.comp (ggQuotHom θ)
  have hπsurj : Function.Surjective π := cP.surjective.comp hπ₀surj
  have hπker : π.ker ≤ Subgroup.center ↥H := by
    have hker : π.ker = (ggQuotHom θ).ker := by
      ext h
      change cP (ggQuotHom θ h) = 1 ↔ ggQuotHom θ h = 1
      exact cP.map_eq_one_iff
    rw [hker, hπ₀ker]
  have hotau_mem : ∀ u : PlaneRaw.V t, otau ζ t δ u ∈ omegaQ (K := K) t δ := by
    intro u
    obtain ⟨a, ha, heq⟩ := (hconj (otau ζ t δ u)).mpr ⟨u, rfl⟩
    rw [heq]
    exact oef_omegaQ_conj_mem t δ hP a.2
  let torusHom : Multiplicative (PlaneRaw.V t) →* ↥Ω :=
    { toFun := fun u => ⟨otau ζ t δ (Multiplicative.toAdd u), hotau_mem _⟩
      map_one' := by
        apply Subtype.ext
        simpa using otau_zero ζ t δ
      map_mul' := by
        intro u v
        apply Subtype.ext
        change otau ζ t δ (Multiplicative.toAdd (u * v)) =
          otau ζ t δ (Multiplicative.toAdd u) * otau ζ t δ (Multiplicative.toAdd v)
        rw [show Multiplicative.toAdd (u * v) =
          Multiplicative.toAdd u + Multiplicative.toAdd v from rfl, otau_add] }
  let T : Subgroup ↥Ω := torusHom.range
  have hAT : A.map cP.toMonoidHom = T := by
    ext x
    constructor
    · intro hx
      rw [Subgroup.mem_map] at hx
      obtain ⟨a, ha, rfl⟩ := hx
      obtain ⟨u, hu⟩ := (hconj (P * ((a : ↥Ω) : GL
        (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) * P⁻¹)).mp ⟨a, ha, rfl⟩
      refine ⟨Multiplicative.ofAdd u, ?_⟩
      apply Subtype.ext
      change otau ζ t δ u = ((cP a : ↥Ω) : GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K)
      rw [hcP a]
      exact hu.symm
    · intro hx
      rw [MonoidHom.mem_range] at hx
      obtain ⟨u, rfl⟩ := hx
      obtain ⟨a, ha, heq⟩ := (hconj (otau ζ t δ (Multiplicative.toAdd u))).mpr
        ⟨Multiplicative.toAdd u, rfl⟩
      refine Subgroup.mem_map.mpr ⟨a, ha, ?_⟩
      apply Subtype.ext
      change ((cP a : ↥Ω) : GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) =
        otau ζ t δ (Multiplicative.toAdd u)
      rw [hcP a]
      exact heq.symm
  let eConj : ↥A ≃* ↥T :=
    (Subgroup.equivMapOfInjective A cP.toMonoidHom
      cP.injective).trans (MulEquiv.subgroupCongr hAT)
  have hotau_inj : Function.Injective (fun u : PlaneRaw.V t => otau ζ t δ u) := by
    intro u v h
    apply oef_liftV_injective t δ
    apply SpBlocks.tau_injective hζinj (t + δ.val)
    exact Subtype.ext h
  let fT : Multiplicative (PlaneRaw.V t) →* ↥T :=
    { toFun := fun u => ⟨torusHom u, ⟨u, rfl⟩⟩
      map_one' := by apply Subtype.ext; simp
      map_mul' := by intro u v; apply Subtype.ext; simp }
  have hfTsurj : Function.Surjective fT := by
    rintro ⟨y, u, rfl⟩
    exact ⟨u, rfl⟩
  have hfTinj : Function.Injective fT := by
    intro u v h
    apply hotau_inj
    exact congrArg (fun x : ↥T =>
      ((x : ↥Ω) : GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K)) h
  let eRange : Multiplicative (PlaneRaw.V t) ≃* ↥T :=
    MulEquiv.ofBijective fT ⟨hfTinj, hfTsurj⟩
  let ePi : (Fin t → Multiplicative (ZMod 3)) ≃* Multiplicative (PlaneRaw.V t) :=
    (MulEquiv.piMultiplicative (fun _ : Fin t => ZMod 3)).symm
  let eT : Multiplicative (PlaneRaw.V t) ≃* ↥A := eRange.trans eConj.symm
  let eρFun : ↥E →* ↥A :=
    { toFun := fun b => ⟨ρ b, ⟨b, rfl⟩⟩
      map_one' := by apply Subtype.ext; simp
      map_mul' := by intro a b; apply Subtype.ext; simp }
  have heρbij : Function.Bijective eρFun := by
    refine ⟨?_, ?_⟩
    · intro a b hab
      exact hρinj (congrArg Subtype.val hab)
    · rintro ⟨y, b, rfl⟩
      exact ⟨b, rfl⟩
  let eρ : ↥E ≃* ↥A := MulEquiv.ofBijective eρFun heρbij
  let τ : (Fin t → Multiplicative (ZMod 3)) ≃* ↥E := ePi.trans (eT.trans eρ.symm)
  have hcardD : Nat.card (Fin t → Multiplicative (ZMod 3)) = 3 ^ t := by
    rw [Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin]
    simp
  have hcardE : Nat.card ↥E = 3 ^ t := by
    rw [← hcardD]
    exact (Nat.card_congr τ.toEquiv).symm
  have heConj_apply : ∀ a : ↥A,
      ((eConj a : ↥T) : GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) =
        P * ((a : ↥Ω) : GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) * P⁻¹ := by
    intro a
    change ((cP (a : ↥Ω) : ↥Ω) : GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) =
      P * ((a : ↥Ω) : GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) * P⁻¹
    exact hcP (a : ↥Ω)
  have heRange_apply : ∀ u : Multiplicative (PlaneRaw.V t),
      ((eRange u : ↥T) : GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) =
        otau ζ t δ (Multiplicative.toAdd u) := by
    intro u
    rfl
  have hePi_toAdd : ∀ u : Fin t → Multiplicative (ZMod 3),
      Multiplicative.toAdd (ePi u) = fun i => Multiplicative.toAdd (u i) := by
    intro u
    simp [ePi]
  have htau_conj : ∀ u : Fin t → Multiplicative (ZMod 3),
      P * ((ρ (τ u) : ↥Ω) : GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) * P⁻¹ =
        otau ζ t δ (fun i => Multiplicative.toAdd (u i)) := by
    intro u
    have h1 : eρ (τ u) = eT (ePi u) := by
      change eρ (eρ.symm (eT (ePi u))) = eT (ePi u)
      rw [MulEquiv.apply_symm_apply]
    have h2 : eConj (eT (ePi u)) = eRange (ePi u) := by
      change eConj (eConj.symm (eRange (ePi u))) = eRange (ePi u)
      rw [MulEquiv.apply_symm_apply]
    have h3 : ((eConj (eT (ePi u)) : ↥T) :
        GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) =
        ((eRange (ePi u) : ↥T) : GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) :=
      congrArg (fun x : ↥T => ((x : ↥Ω) :
        GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K)) h2
    rw [heConj_apply, heRange_apply] at h3
    have h4 : P * ((eT (ePi u) : ↥A) :
        GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) * P⁻¹ =
        otau ζ t δ (fun i => Multiplicative.toAdd (u i)) := by
      simpa [hePi_toAdd] using h3
    have h5 : ((eT (ePi u) : ↥A) :
        GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) =
        ((ρ (τ u) : ↥Ω) : GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) := by
      rw [← h1]
      rfl
    rwa [h5] at h4
  have hπ_apply : ∀ h : ↥H, ((π h : ↥Ω) :
      GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) =
      P * ((ggQuotHom θ h : ↥Ω) : GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) * P⁻¹ :=
    fun h => hcP (ggQuotHom θ h)
  refine ⟨ζ, hζinj, hcardE, ⟨{
    π := π
    surj := hπsurj
    ker_le := hπker
    τ := τ
    intertwine := ?_ }⟩⟩
  intro u h
  let b : ↥E := τ u
  have hb : P * ((ρ b : ↥Ω) : GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) * P⁻¹ =
      otau ζ t δ (fun i => Multiplicative.toAdd (u i)) := htau_conj u
  have hρb := hρ b h
  calc ((π (H.normalizerMonoidHom ⟨(b : G), hEN b.2⟩ h) : ↥Ω) :
        GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K)
      = P * ((ggQuotHom θ (H.normalizerMonoidHom ⟨(b : G), hEN b.2⟩ h) : ↥Ω) :
          GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) * P⁻¹ := hπ_apply _
    _ = P * ((ρ b * ggQuotHom θ h * (ρ b)⁻¹ : ↥Ω) :
          GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) * P⁻¹ := by rw [hρb]
    _ = (P * ((ρ b : ↥Ω) : GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) * P⁻¹) *
          (P * ((ggQuotHom θ h : ↥Ω) :
            GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) * P⁻¹) *
          (P * ((ρ b : ↥Ω) : GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) * P⁻¹)⁻¹ := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        group
    _ = otau ζ t δ (fun i => Multiplicative.toAdd (u i)) *
          ((π h : ↥Ω) : GL (Fin (t + δ.val) ⊕ Fin (t + δ.val)) K) *
          (otau ζ t δ (fun i => Multiplicative.toAdd (u i)))⁻¹ := by
        rw [hb, hπ_apply h]

end

end CFSG.StandardType.GGQ2Frame.OrthPlacement
