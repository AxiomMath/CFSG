module

public import CFSG.LocalAnalysis.StandardType.TableC.HypDefs
import CFSG.ClassicalInvolution.ModelFacts.UnitaryAutLift
import CFSG.LocalAnalysis.StandardType.GGInnerDiagMpStdTwE6
import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitTwE6Tag

public section

namespace CFSG.StandardType.TableCRes

open CFSG.Assembly CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.StandardType CFSG.Open

section CentreConj

variable {X : Type} [Group X] [Finite X] {G₀ : Subgroup X}

private theorem w6C_conjAut_eq_one {a : X}
    (hanorm : a ∈ Subgroup.normalizer (G₀ : Set X)) (ha3 : a ^ 3 = 1)
    (hZcard : Nat.card (Subgroup.center ↥G₀) = 3) :
    ∀ z : ↥G₀, z ∈ Subgroup.center ↥G₀ → a * (z : X) * a⁻¹ = (z : X) := by
  classical
  set Z : Subgroup ↥G₀ := Subgroup.center ↥G₀ with hZdef
  have hmem : ∀ z : ↥G₀, a * (z : X) * a⁻¹ ∈ G₀ := fun z =>
    (Subgroup.mem_normalizer_iff.mp hanorm (z : X)).mp z.2
  have hmemInv : ∀ z : ↥G₀, a⁻¹ * (z : X) * a ∈ G₀ := fun z => by
    have h := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hanorm) (z : X)).mp z.2
    simpa using h
  have hcent : ∀ z : ↥G₀, z ∈ Z →
      (⟨a * (z : X) * a⁻¹, hmem z⟩ : ↥G₀) ∈ Z := by
    intro z hz
    rw [Subgroup.mem_center_iff]
    intro w
    apply Subtype.ext
    have hw : a⁻¹ * (w : X) * a ∈ G₀ := hmemInv w
    have hcomm : (⟨a⁻¹ * (w : X) * a, hw⟩ : ↥G₀) * z =
        z * ⟨a⁻¹ * (w : X) * a, hw⟩ :=
      (Subgroup.mem_center_iff.mp hz) ⟨a⁻¹ * (w : X) * a, hw⟩
    have hcommX : (a⁻¹ * (w : X) * a) * (z : X) =
        (z : X) * (a⁻¹ * (w : X) * a) := congrArg Subtype.val hcomm
    change (w : X) * (a * (z : X) * a⁻¹) = (a * (z : X) * a⁻¹) * (w : X)
    calc (w : X) * (a * (z : X) * a⁻¹)
        = a * ((a⁻¹ * (w : X) * a) * (z : X)) * a⁻¹ := by group
      _ = a * ((z : X) * (a⁻¹ * (w : X) * a)) * a⁻¹ := by rw [hcommX]
      _ = (a * (z : X) * a⁻¹) * (w : X) := by group
  have hcentInv : ∀ z : ↥G₀, z ∈ Z →
      (⟨a⁻¹ * (z : X) * a, hmemInv z⟩ : ↥G₀) ∈ Z := by
    intro z hz
    rw [Subgroup.mem_center_iff]
    intro w
    apply Subtype.ext
    have hw : a * (w : X) * a⁻¹ ∈ G₀ := hmem w
    have hcomm : (⟨a * (w : X) * a⁻¹, hw⟩ : ↥G₀) * z =
        z * ⟨a * (w : X) * a⁻¹, hw⟩ :=
      (Subgroup.mem_center_iff.mp hz) ⟨a * (w : X) * a⁻¹, hw⟩
    have hcommX : (a * (w : X) * a⁻¹) * (z : X) =
        (z : X) * (a * (w : X) * a⁻¹) := congrArg Subtype.val hcomm
    change (w : X) * (a⁻¹ * (z : X) * a) = (a⁻¹ * (z : X) * a) * (w : X)
    calc (w : X) * (a⁻¹ * (z : X) * a)
        = a⁻¹ * ((a * (w : X) * a⁻¹) * (z : X)) * a := by group
      _ = a⁻¹ * ((z : X) * (a * (w : X) * a⁻¹)) * a := by rw [hcommX]
      _ = (a⁻¹ * (z : X) * a) * (w : X) := by group
  let f : ↥Z →* ↥Z :=
    { toFun := fun z => ⟨⟨a * (z.1 : X) * a⁻¹, hmem z.1⟩, hcent z.1 z.2⟩
      map_one' := by
        apply Subtype.ext
        apply Subtype.ext
        show a * ((1 : ↥G₀) : X) * a⁻¹ = ((1 : ↥G₀) : X)
        simp only [Subgroup.coe_one]
        group
      map_mul' := by
        intro x y
        apply Subtype.ext
        apply Subtype.ext
        show a * ((x.1 * y.1 : ↥G₀) : X) * a⁻¹ =
          (a * (x.1 : X) * a⁻¹) * (a * (y.1 : X) * a⁻¹)
        simp only [Subgroup.coe_mul]
        group }
  have hinj : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    have h : a * (x.1 : X) * a⁻¹ = a * (y.1 : X) * a⁻¹ := by
      have hc := congrArg (fun t : ↥Z => ((t.1 : ↥G₀) : X)) hxy
      simpa [f] using hc
    calc (x.1 : X) = a⁻¹ * (a * (x.1 : X) * a⁻¹) * a := by group
      _ = a⁻¹ * (a * (y.1 : X) * a⁻¹) * a := by rw [h]
      _ = (y.1 : X) := by group
  have hsurj : Function.Surjective f := by
    intro y
    refine ⟨⟨⟨a⁻¹ * (y.1 : X) * a, hmemInv y.1⟩, hcentInv y.1 y.2⟩, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    show a * (a⁻¹ * (y.1 : X) * a) * a⁻¹ = (y.1 : X)
    group
  let φ : MulAut ↥Z := MulEquiv.ofBijective f ⟨hinj, hsurj⟩
  have hφ3 : φ ^ 3 = 1 := by
    ext z
    show a * (a * (a * (z.1 : X) * a⁻¹) * a⁻¹) * a⁻¹ = (z.1 : X)
    calc a * (a * (a * (z.1 : X) * a⁻¹) * a⁻¹) * a⁻¹
        = (a * a * a) * (z.1 : X) * (a * a * a)⁻¹ := by group
      _ = (z.1 : X) := by
        rw [show a * a * a = a ^ 3 by rw [pow_succ, pow_two], ha3]
        group
  have hdvd3 : orderOf φ ∣ 3 :=
    orderOf_dvd_iff_pow_eq_one.mpr hφ3
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcyc : IsCyclic ↥Z := isCyclic_of_prime_card (by simpa using hZcard)
  have haut : Nat.card (MulAut ↥Z) = Nat.totient (Nat.card ↥Z) :=
    IsCyclic.card_mulAut ↥Z
  have haut2 : Nat.card (MulAut ↥Z) = 2 := by
    rw [haut, hZcard, Nat.totient_prime Nat.prime_three]
  have hdvd2 : orderOf φ ∣ 2 := by
    rw [← haut2]
    exact orderOf_dvd_natCard φ
  have hdvd1 : orderOf φ ∣ 1 := by
    have h := Nat.dvd_gcd hdvd3 hdvd2
    simpa using h
  have hone : φ = 1 := orderOf_eq_one_iff.mp (Nat.dvd_one.mp hdvd1)
  intro z hz
  have h1 : ((φ ⟨z, hz⟩).1 : X) = (z : X) := by
    have h := congrArg (fun e : MulAut ↥Z => ((e ⟨z, hz⟩).1 : X)) hone
    simpa using h
  have h2 : ((φ ⟨z, hz⟩).1 : X) = a * (z : X) * a⁻¹ := by
    change (((f ⟨z, hz⟩).1 : ↥G₀) : X) = a * (z : X) * a⁻¹
    rfl
  rw [← h2]
  exact h1


end CentreConj

section Centre

variable {X : Type} [Group X] [Finite X] {n f p : ℕ} {G₀ B D J L : Subgroup X} {x : X}

private noncomputable def w6C_codRestrict
    {ψ : (ggU .twistedE6 n f).K →* X}
    (h : GGTCHyp .twistedE6 n f ψ p G₀ B D J L x) :
    (ggU .twistedE6 n f).K →* ↥G₀ :=
  ψ.codRestrict G₀ fun u => by
    rw [← h.range]
    exact ⟨u, rfl⟩

private theorem w6C_center_le_map_center
    {ψ : (ggU .twistedE6 n f).K →* X}
    (h : GGTCHyp .twistedE6 n f ψ p G₀ B D J L x) :
    Subgroup.center ↥G₀ ≤
      (Subgroup.center (ggU .twistedE6 n f).K).map (w6C_codRestrict h) := by
  have hsurj : Function.Surjective (w6C_codRestrict h) := by
    intro y
    have hy : (y : X) ∈ ψ.range := by
      rw [h.range]
      exact y.2
    obtain ⟨u, hu⟩ := hy
    exact ⟨u, Subtype.ext hu⟩
  have hker : (w6C_codRestrict h).ker ≤ Subgroup.center (ggU .twistedE6 n f).K := by
    intro u hu
    exact h.ker (by simpa [w6C_codRestrict] using congrArg Subtype.val hu)
  have hperf : Group.IsPerfect (ggU .twistedE6 n f).K :=
    Group.IsPerfect.mk (MpStdTwE6.commutator_twistedE6Group h.adm.2.1)
  exact CFSG.ClassicalInvolution.ModelFacts.UnitaryAut.center_le_map_center_of_perfect
    hsurj hker

private theorem w6C_map_center_le_center
    {ψ : (ggU .twistedE6 n f).K →* X}
    (h : GGTCHyp .twistedE6 n f ψ p G₀ B D J L x) :
    (Subgroup.center (ggU .twistedE6 n f).K).map (w6C_codRestrict h) ≤
      Subgroup.center ↥G₀ := by
  intro z hz
  rw [Subgroup.mem_map] at hz
  obtain ⟨u, hu, rfl⟩ := hz
  rw [Subgroup.mem_center_iff]
  intro w
  apply Subtype.ext
  obtain ⟨v, hv⟩ : ∃ v, ψ v = (w : X) := by
    have hw : (w : X) ∈ ψ.range := by
      rw [h.range]
      exact w.2
    exact hw
  have huv : v * u = u * v := (Subgroup.mem_center_iff.mp hu) v
  calc (w : X) * ψ u = ψ v * ψ u := by rw [hv]
    _ = ψ (v * u) := (map_mul ψ v u).symm
    _ = ψ (u * v) := by rw [huv]
    _ = ψ u * ψ v := map_mul ψ u v
    _ = ψ u * (w : X) := by rw [hv]

private theorem w6C_center_card_dvd_three
    {ψ : (ggU .twistedE6 n f).K →* X}
    (h : GGTCHyp .twistedE6 n f ψ p G₀ B D J L x) :
    Nat.card (Subgroup.center ↥G₀) ∣ 3 := by
  have heq : Subgroup.center ↥G₀ =
      (Subgroup.center (ggU .twistedE6 n f).K).map (w6C_codRestrict h) :=
    le_antisymm (w6C_center_le_map_center h) (w6C_map_center_le_center h)
  let φ : ↥(Subgroup.center (ggU .twistedE6 n f).K) →*
      ↥(Subgroup.center ↥G₀) :=
    ((w6C_codRestrict h).comp (Subgroup.center (ggU .twistedE6 n f).K).subtype).codRestrict
      (Subgroup.center ↥G₀) fun u =>
        (w6C_map_center_le_center h) (Subgroup.mem_map.mpr ⟨u.1, u.2, rfl⟩)
  have hsurj : Function.Surjective φ := by
    intro z
    have hz : (z : ↥G₀) ∈
        (Subgroup.center (ggU .twistedE6 n f).K).map (w6C_codRestrict h) := by
      rw [← heq]
      exact z.2
    obtain ⟨u, hu, huz⟩ := Subgroup.mem_map.mp hz
    exact ⟨⟨u, hu⟩, Subtype.ext huz⟩
  have hrange : φ.range = ⊤ := MonoidHom.range_eq_top.mpr hsurj
  have hdvd : Nat.card ↥(Subgroup.center ↥G₀) ∣
      Nat.card ↥(Subgroup.center (ggU .twistedE6 n f).K) := by
    have h := Subgroup.card_range_dvd φ
    rwa [hrange, Subgroup.card_top] at h
  exact hdvd.trans (TwE6Nonsplit.center_card_dvd_three f h.adm.2.1)

theorem GGTCHyp.center_eq_bot_twE6
    {ψ : (ggU .twistedE6 n f).K →* X}
    (h : GGTCHyp .twistedE6 n f ψ p G₀ B D J L x) (hp : p = 3) :
    Subgroup.center ↥G₀ = ⊥ := by
  by_contra hne
  obtain ⟨zZ, hzZne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  let z : ↥G₀ := zZ.1
  have hz : z ∈ Subgroup.center ↥G₀ := zZ.2
  have hz1 : z ≠ 1 := by
    intro hz_eq
    exact hzZne (Subtype.ext hz_eq)
  have hZcard : Nat.card (Subgroup.center ↥G₀) = 3 := by
    have hdvd := w6C_center_card_dvd_three h
    have hne1 : Nat.card (Subgroup.center ↥G₀) ≠ 1 := by
      intro hc
      exact hne (Subgroup.eq_bot_of_card_eq (Subgroup.center ↥G₀) hc)
    rcases Nat.Prime.eq_one_or_self_of_dvd Nat.prime_three
      (Nat.card (Subgroup.center ↥G₀)) hdvd with h1 | h3
    · exact absurd h1 hne1
    · exact h3
  have horder : orderOf z = 3 := by
    have hdvd : orderOf z ∣ 3 := by
      have h := Subgroup.orderOf_dvd_natCard (Subgroup.center ↥G₀) hz
      rwa [hZcard] at h
    rcases Nat.Prime.eq_one_or_self_of_dvd Nat.prime_three (orderOf z) hdvd with h1 | h3
    · exact absurd h1 (by intro h; exact hz1 (orderOf_eq_one_iff.mp h))
    · exact h3
  obtain ⟨A, -, hAel, hAnorm, -, hAinf, hAord, -⟩ := h.e6 (Or.inr rfl)
  have hzcentA : (z : X) ∈ Subgroup.centralizer (A : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    have hanorm : a ∈ Subgroup.normalizer (G₀ : Set X) := hAnorm ha
    have ha3 : a ^ 3 = 1 := by
      have h := hAel.2 a ha
      rwa [hp] at h
    have hconj := w6C_conjAut_eq_one hanorm ha3 hZcard z hz
    calc a * (z : X) = (a * (z : X) * a⁻¹) * a := by group
      _ = (z : X) * a := by rw [hconj]
  have hzcent : (z : X) ∈ Subgroup.centralizer (G₀ : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨g, hg⟩)
  have hzA : (z : X) ∈ A := by
    apply hAord (z : X) ?_ ?_
    · exact Subgroup.mem_inf.mpr ⟨Subgroup.mem_sup_right z.2, hzcentA⟩
    · rw [Subgroup.orderOf_coe, horder, hp]
  have hzb : (z : X) ∈ (⊥ : Subgroup X) := by
    rw [← hAinf]
    exact Subgroup.mem_inf.mpr ⟨hzA, hzcent⟩
  rw [Subgroup.mem_bot] at hzb
  exact hz1 (Subtype.ext hzb)

end Centre

end CFSG.StandardType.TableCRes

end
