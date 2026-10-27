module

public import CFSG.RankThree.PartOne.KEXC.D8Scalar
public import CFSG.RankThree.PartOne.KEXC.WeylScalar
public import CFSG.RankThree.PartOne.KFOUT3.KtySUQuot
public import CFSG.RankThree.PartOne.KF.D8Ctx

public section

namespace CFSG.RankThree.PartOne.KEXC

open CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KFU CFSG.RankThree.PartOne.KFOUT3

section Map

variable {Q Q' : Type} [Group Q] [Group Q']

theorem bigAt_map {p : ℕ} {u : Q} {R : ℕ → Prop} (h : BigAt p u R) (e : Q ≃* Q') :
    BigAt p (e u) R := by
  obtain ⟨S', hperf, hsimple, ⟨σ, hσ, hσp⟩, hc, hn, hM⟩ := h
  have hinj : Function.Injective e.toMonoidHom := e.injective
  let e' : ↥S' ≃* ↥(S'.map e.toMonoidHom) := S'.equivMapOfInjective _ hinj
  refine ⟨S'.map e.toMonoidHom, ?_, ?_, ⟨e σ, ⟨σ, hσ, rfl⟩, ?_⟩, ?_, ?_, ?_⟩
  · have := hperf
    exact Group.IsPerfect.map _
  · exact e'.symm.isSimpleGroup
  · rw [MulEquiv.orderOf_eq]
    exact hσp
  · rintro _ ⟨σ', hσ', rfl⟩
    show e u * e σ' = e σ' * e u
    rw [← map_mul, ← map_mul, hc σ' hσ']
  · intro x hx
    rintro _ ⟨σ', hσ', rfl⟩
    have hx' : u * e.symm x = e.symm x * u := by
      have := congrArg e.symm hx
      simpa using this
    refine ⟨e.symm x * σ' * (e.symm x)⁻¹, hn _ hx' σ' hσ', ?_⟩
    show e (e.symm x * σ' * (e.symm x)⁻¹) = x * e σ' * x⁻¹
    simp
  · rw [Subgroup.card_map_of_injective hinj]
    exact hM

theorem bigAt_smallAt_false {p : ℕ} {u : Q} {R : ℕ → Prop} (hb : BigAt p u R)
    (hs : SmallAt u R) : False := by
  obtain ⟨S', hperf, -, -, hc, -, hR⟩ := hb
  exact hs S' hperf hc _ hR (dvd_refl _)

end Map

section Factor

variable {L Q : Type} [Group L] [Group Q] {p : ℕ}

theorem exists_centralQuot_factor {ε : L →* Q} (hε : IsCentralPQuot p ε)
    (hcop : Nat.Coprime p (Nat.card (Subgroup.center L))) :
    ∃ ρ : Q →* L ⧸ Subgroup.center L, IsCentralPQuot p ρ ∧
      ∀ x : L, ρ (ε x) = (x : L ⧸ Subgroup.center L) := by
  classical
  let e := QuotientGroup.quotientKerEquivOfSurjective ε hε.surjective
  have he : ∀ x : L, e (QuotientGroup.mk x) = ε x := fun x => rfl
  let lift : (L ⧸ ε.ker) →* (L ⧸ Subgroup.center L) :=
    QuotientGroup.lift ε.ker (QuotientGroup.mk' (Subgroup.center L)) (fun x hx => by
      rw [QuotientGroup.ker_mk']
      exact hε.central hx)
  let ρ : Q →* L ⧸ Subgroup.center L := lift.comp e.symm.toMonoidHom
  have hρ : ∀ x : L, ρ (ε x) = (x : L ⧸ Subgroup.center L) := by
    intro x
    have h1 : e.symm (ε x) = QuotientGroup.mk x := (MulEquiv.symm_apply_eq e).mpr (he x).symm
    show lift (e.symm (ε x)) = _
    rw [h1]
    rfl
  have hker : ∀ q : Q, q ∈ ρ.ker → ∃ z ∈ Subgroup.center L, ε z = q := by
    intro q hq
    obtain ⟨x, rfl⟩ := hε.surjective q
    refine ⟨x, ?_, rfl⟩
    rw [MonoidHom.mem_ker, hρ] at hq
    exact (QuotientGroup.eq_one_iff x).mp hq
  refine ⟨ρ, ⟨?_, ?_, ?_⟩, hρ⟩
  · intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    exact ⟨ε x, hρ x⟩
  · intro q hq
    obtain ⟨z, hz, rfl⟩ := hker q hq
    rw [Subgroup.mem_center_iff]
    intro q'
    obtain ⟨x', rfl⟩ := hε.surjective q'
    rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.mp hz x').symm]
  · have hle : ρ.ker ≤ (Subgroup.center L).map ε := fun q hq => by
      obtain ⟨z, hz, rfl⟩ := hker q hq
      exact ⟨z, hz, rfl⟩
    exact Nat.Coprime.coprime_dvd_right
      ((Subgroup.card_dvd_of_le hle).trans (Subgroup.card_map_dvd _ ε)) hcop

end Factor

section Main

variable {G : Type} [Group G] {p : ℕ} {K : Type} [Field K] {L F : Subgroup G}

theorem d8_weyl_scalar (hp : p.Prime) (hp2 : p ≠ 2) (hζ : ∃ ζ : Kˣ, IsPrimitiveRoot ζ p)
    (hcop : Nat.Coprime p (Nat.card (Subgroup.center ↥L))) (hFL : F ≤ L) (S : D8Ctx p K L F)
    {Q : Type} [Group Q] {ε : ↥L →* Q} (hε : IsCentralPQuot p ε) (Temb : D8Mod p K →* Q)
    (hrel : ∀ d, ε (Subgroup.inclusion hFL (S.tor d)) = Temb d)
    (Hconj : ∀ γ : DihedralGroup 4, ∃ m : Q, ∀ v, m * Temb v * m⁻¹ = Temb (d8Act γ v))
    {R : ℕ → Prop} (Hsmall : ∀ b : rootsOfUnity p K, b ≠ 1 → SmallAt (Temb (1, b)) R)
    (Hbig : ∀ a : rootsOfUnity p K, a ≠ 1 → BigAt p (Temb (a, a)) R)
    {y : G} (hyL : y ∈ Subgroup.normalizer (L : Set G))
    (hyF : y ∈ Subgroup.normalizer (F : Set G)) :
    ∃ h : G, h ∈ L ∧ h ∈ Subgroup.normalizer (F : Set G) ∧
      ∃ k : ℤ, ∀ f ∈ F, y * f * y⁻¹ = h * f ^ k * h⁻¹ := by
  classical
  obtain ⟨ρ, hρ, hρε⟩ := exists_centralQuot_factor hε hcop
  have hVexp : ∀ d : D8Mod p K, d ^ p = 1 := fun d =>
    Prod.ext (Subtype.ext ((mem_rootsOfUnity p _).mp d.1.2))
      (Subtype.ext ((mem_rootsOfUnity p _).mp d.2.2))
  have hTpow : ∀ v : D8Mod p K, Temb v ^ p = 1 := fun v => by
    rw [← map_pow, hVexp, map_one]
  have hBigQ : ∀ v : D8Mod p K, BigVec v → BigAt p (Temb v) R := by
    rintro v ⟨h1, h2 | h2⟩
    · have : v = (v.1, v.1) := Prod.ext rfl h2
      rw [this]
      exact Hbig _ h1
    · obtain ⟨m, hm⟩ := Hconj (DihedralGroup.r 1)
      have hvs : v = d8Act (DihedralGroup.r 1) (v.1, v.1) := by
        rw [d8Act_r_one]
        exact Prod.ext rfl h2
      have : Temb v = m * Temb (v.1, v.1) * m⁻¹ := by rw [hm, ← hvs]
      rw [this]
      exact (Hbig _ h1).conj m
  have hSmallQ : ∀ v : D8Mod p K, SmallVec v → SmallAt (Temb v) R := by
    rintro v (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · have : v = (1, v.2) := Prod.ext h1 rfl
      rw [this]
      exact Hsmall _ h2
    · obtain ⟨m, hm⟩ := Hconj (DihedralGroup.sr 3)
      have hvt : v = d8Act (DihedralGroup.sr 3) (1, v.1) := by
        rw [d8Act_sr_three]
        exact Prod.ext rfl h1
      have : Temb v = m * Temb (1, v.1) * m⁻¹ := by rw [hm, ← hvt]
      rw [this]
      exact (Hsmall _ h2).conj m
  have hBigρ : ∀ v : D8Mod p K, BigVec v → BigAt p (ρ (Temb v)) R := by
    intro v hv
    obtain ⟨S', hperf, hsimple, hord, hc, hn, hR⟩ := hBigQ v hv
    exact bigAt_of_central hp hρ (hTpow v) hperf hsimple hord hc hn hR
  have hSmallρ : ∀ v : D8Mod p K, SmallVec v → SmallAt (ρ (Temb v)) R := fun v hv =>
    smallAt_of_central hρ (hTpow v) (hSmallQ v hv)
  set c : MulAut ↥L := L.normalizerMonoidHom ⟨y, hyL⟩ with hc
  let ybar : MulAut (↥L ⧸ Subgroup.center ↥L) :=
    QuotientGroup.congr (Subgroup.center ↥L) (Subgroup.center ↥L) c (Subgroup.map_center_eq c)
  have hybar : ∀ x : ↥L, ybar (x : ↥L ⧸ Subgroup.center ↥L) =
      ((c x : ↥L) : ↥L ⧸ Subgroup.center ↥L) := fun x =>
    QuotientGroup.congr_mk _ _ c _ x
  have hincl : ∀ v : D8Mod p K, Subgroup.inclusion hFL (S.tor (weylConjAut S hyF v)) =
      c (Subgroup.inclusion hFL (S.tor v)) := fun v =>
    Subtype.ext (coe_tor_weylConjAut S hyF v)
  have hmodel : ∀ v : D8Mod p K, ybar (ρ (Temb v)) = ρ (Temb (weylConjAut S hyF v)) := by
    intro v
    rw [← hrel v, ← hrel (weylConjAut S hyF v), hρε, hρε, hybar, hincl]
  have hcls : ∀ v : D8Mod p K, BigVec v → ¬ SmallVec (weylConjAut S hyF v) := by
    intro v hv hsm
    have h2 := bigAt_map (hBigρ v hv) ybar
    rw [hmodel v] at h2
    exact bigAt_smallAt_false h2 (hSmallρ _ hsm)
  exact exists_scalar_of_weylConjAut S hyF
    (exists_d8Act_mul_pow hp hp2 hζ _ (S.normalizes_act hyL hyF) hcls)

end Main

end CFSG.RankThree.PartOne.KEXC
