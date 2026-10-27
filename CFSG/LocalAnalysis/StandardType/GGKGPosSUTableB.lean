module

public import CFSG.LocalAnalysis.StandardType.GGKGPosSUStd
public import CFSG.LocalAnalysis.StandardType.GGKGPosSURankOne
public import CFSG.LocalAnalysis.StandardType.GGSecFivePresTagUnitary
public import CFSG.LocalAnalysis.StandardType.GGF4QGeFourKGPos
import Mathlib.Tactic.Group

public section

namespace CFSG.StandardType.KGPosSU

open CFSG.LieType.Universal CFSG.LieType.Universal.Unitary
  CFSG.LieType.Universal.Unitary.SUExtras CFSG.LieType.BorelTits CFSG.LieType.Steinberg
  CFSG.LieType.CurtisTits CFSG.LieType.RootSystem CFSG.Assembly CFSG.Open
  CFSG.StandardType.TableCRes

theorem ggOTwoPrime_map_of_odd_ker {H G : Type*} [Group H] [Group G] (ψ : H →* G) {N : ℕ}
    (hN : Odd N) (hker : ∀ z ∈ ψ.ker, z ^ N = 1) (Y : Subgroup H) :
    ggOTwoPrime (Y.map ψ) = (ggOTwoPrime Y).map ψ := by
  apply le_antisymm
  · rw [ggOTwoPrime, Subgroup.closure_le]
    rintro _ ⟨⟨z, hzY, rfl⟩, m, hm⟩
    have h1 : z ^ 2 ^ m ∈ ψ.ker := by rw [MonoidHom.mem_ker, map_pow, hm]
    have h2 : (z ^ N) ^ 2 ^ m = 1 := by rw [← pow_mul, mul_comm, pow_mul, hker _ h1]
    have h3 : z ^ N ∈ ggOTwoPrime Y := Subgroup.subset_closure ⟨pow_mem hzY N, m, h2⟩
    have hcop : N.Coprime (orderOf (ψ z)) :=
      Nat.Coprime.coprime_dvd_right (orderOf_dvd_of_pow_eq_one hm)
        ((Nat.coprime_two_right.mpr hN).pow_right m)
    obtain ⟨M, hM⟩ := exists_pow_eq_self_of_coprime hcop
    rw [← hM]
    refine pow_mem ?_ M
    rw [← map_pow]
    exact Subgroup.mem_map_of_mem ψ h3
  · rw [ggOTwoPrime, MonoidHom.map_closure]
    refine Subgroup.closure_mono ?_
    rintro _ ⟨y, ⟨hyY, k, hk⟩, rfl⟩
    exact ⟨⟨y, hyY, rfl⟩, k, by rw [← map_pow, hk, map_one]⟩

section Chart

theorem commute_of_map_commute {G : Type*} [Group G] {p t : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ 2 ^ (t + 1) - 1) {ψ : ↥(Unitary.SU (PSUσ t) 6) →* G}
    (hker : ψ.ker ≤ Subgroup.center _) {u s : ↥(Unitary.SU (PSUσ t) 6)}
    (hs : s ∈ diagP (PSUF t) (t + 1) p) (h : ψ u * ψ s = ψ s * ψ u) : u * s = s * u := by
  have hck : u * s * u⁻¹ * s⁻¹ ∈ ψ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, h]
    group
  have hcZ := hker hck
  have hcp : (u * s * u⁻¹ * s⁻¹) ^ p = 1 := by
    have h1 : (u * s * u⁻¹) ^ p = 1 := by rw [conj_pow, hs.2, mul_one, mul_inv_cancel]
    have h2 : ((u * s * u⁻¹ * s⁻¹) * s) ^ p = (u * s * u⁻¹ * s⁻¹) ^ p := by
      rw [Commute.mul_pow (Subgroup.mem_center_iff.mp hcZ s).symm, hs.2, mul_one]
    rw [← h2, inv_mul_cancel_right, h1]
  have hc1 := eq_one_of_mem_center_of_pow_eq_one (card_PSUF t) hp hp2 hpq hcZ hcp
  calc u * s = u * s * u⁻¹ * s⁻¹ * s * u := by group
    _ = s * u := by rw [hc1, one_mul]

theorem exists_tableB_chart {G : Type} [Group G] [Finite G] {p t : ℕ} {Bs X : Subgroup G}
    (ψ : ↥(Unitary.SU (PSUσ t) 6) →* G) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ 2 ^ (t + 1) - 1) (hker : ψ.ker ≤ Subgroup.center _) (hrange : ψ.range = X)
    (hBs : IsElemAbelian p Bs)
    (hC3 : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (ℓ : ↥Bs →* ↥(Unitary.SU (PSUσ t) 6))
    (hℓ : ∀ (b : ↥Bs) (u : ↥(Unitary.SU (PSUσ t) 6)),
      (b : G)⁻¹ * ψ u * (b : G) = ψ (ℓ b * u * (ℓ b)⁻¹))
    (hℓT : ∀ b, ℓ b ∈ diagP (PSUF t) (t + 1) p) (hrank : p ^ 3 ≤ Nat.card ℓ.range)
    {ν : GGWeyl (Unitary.rootDatum (card_PSUF t) 6) →* ↥(Unitary.SU (PSUσ t) 6)}
    (hν : GGWeylLift (Unitary.rootDatum (card_PSUF t) 6) ν) :
    ∃ ε : GGWeyl (Unitary.rootDatum (card_PSUF t) 6) ≃* ↥(ggAutomizer X Bs),
      (∀ i, GGIsReflection p ((ε ((coxeterMatrix
        (Unitary.rootDatum (card_PSUF t) 6).isFiniteType).simple i) : ↥(ggAutomizer X Bs)) :
          MulAut ↥Bs)) ∧
      ∀ (w : GGWeyl (Unitary.rootDatum (card_PSUF t) 6)) (i : Fin (6 / 2)),
        ggRankOneIn X Bs ((ε (w * (coxeterMatrix
          (Unitary.rootDatum (card_PSUF t) 6).isFiniteType).simple i * w⁻¹) :
            ↥(ggAutomizer X Bs)) : MulAut ↥Bs) =
          (ggRootLevi (Unitary.rootDatum (card_PSUF t) 6) (weylAction
            (Unitary.rootDatum (card_PSUF t) 6).isFiniteType w (Pi.single i 1))).map ψ := by
  have hF := card_PSUF t
  have hcX : ∀ (b : G) (hb : b ∈ Bs) (u : ↥(Unitary.SU (PSUσ t) 6)),
      b * ψ (ℓ ⟨b, hb⟩) * ψ u = ψ u * (b * ψ (ℓ ⟨b, hb⟩)) := by
    intro b hb u
    have h : b⁻¹ * ψ u * b = ψ (ℓ ⟨b, hb⟩ * u * (ℓ ⟨b, hb⟩)⁻¹) := hℓ ⟨b, hb⟩ u
    rw [map_mul, map_mul, map_inv] at h
    calc b * ψ (ℓ ⟨b, hb⟩) * ψ u =
        b * (ψ (ℓ ⟨b, hb⟩) * ψ u * (ψ (ℓ ⟨b, hb⟩))⁻¹) * ψ (ℓ ⟨b, hb⟩) := by group
      _ = b * (b⁻¹ * ψ u * b) * ψ (ℓ ⟨b, hb⟩) := by rw [h]
      _ = ψ u * (b * ψ (ℓ ⟨b, hb⟩)) := by group
  have hdiagC : ∀ h ∈ diagSubgroup (PSUσ t) 6, ∀ b ∈ Bs, b * ψ h = ψ h * b := by
    intro h hh b hb
    have h1 : b⁻¹ * ψ h * b = ψ (ℓ ⟨b, hb⟩ * h * (ℓ ⟨b, hb⟩)⁻¹) := hℓ ⟨b, hb⟩ h
    rw [commute_of_mem_diagSubgroup (hℓT ⟨b, hb⟩).1 hh, mul_inv_cancel_right] at h1
    calc b * ψ h = b * (b⁻¹ * ψ h * b) := by rw [h1]
      _ = ψ h * b := by group
  have hψT : ∀ s ∈ diagP (PSUF t) (t + 1) p, ψ s ∈ Bs := fun s hs =>
    hC3 _ (Subgroup.mem_centralizer_iff.mpr fun b hb => hdiagC s hs.1 b hb)
      (by rw [← map_pow, hs.2, map_one])
  have htrick : ∀ {u s : ↥(Unitary.SU (PSUσ t) 6)}, s ∈ diagP (PSUF t) (t + 1) p →
      ψ u * ψ s = ψ s * ψ u → u * s = s * u := fun hs h =>
    commute_of_map_commute hp hp2 hpq hker hs h
  have hlift : ∀ (c : G) (hc : c ∈ Bs) (v : ↥(Unitary.SU (PSUσ t) 6)), c * ψ v = ψ v * c →
      ψ v * ψ (ℓ ⟨c, hc⟩) = ψ (ℓ ⟨c, hc⟩) * ψ v := by
    intro c hc v hcv
    have hC := hcX c hc v
    have h2 : ψ v * c⁻¹ = c⁻¹ * ψ v := by
      calc ψ v * c⁻¹ = c⁻¹ * (c * ψ v) * c⁻¹ := by group
        _ = c⁻¹ * (ψ v * c) * c⁻¹ := by rw [hcv]
        _ = c⁻¹ * ψ v := by group
    calc ψ v * ψ (ℓ ⟨c, hc⟩) = ψ v * c⁻¹ * (c * ψ (ℓ ⟨c, hc⟩)) := by group
      _ = c⁻¹ * (ψ v * (c * ψ (ℓ ⟨c, hc⟩))) := by rw [h2]; group
      _ = c⁻¹ * (c * ψ (ℓ ⟨c, hc⟩) * ψ v) := by rw [hC]
      _ = ψ (ℓ ⟨c, hc⟩) * ψ v := by group
  have hunlift : ∀ (c : G) (hc : c ∈ Bs) (v : ↥(Unitary.SU (PSUσ t) 6)),
      ψ (ℓ ⟨c, hc⟩) * ψ v = ψ v * ψ (ℓ ⟨c, hc⟩) → ψ v * c * (ψ v)⁻¹ = c := by
    intro c hc v h4
    have hC := hcX c hc v
    calc ψ v * c * (ψ v)⁻¹ =
        ψ v * (c * ψ (ℓ ⟨c, hc⟩)) * (ψ (ℓ ⟨c, hc⟩))⁻¹ * (ψ v)⁻¹ := by group
      _ = c * ψ (ℓ ⟨c, hc⟩) * ψ v * (ψ (ℓ ⟨c, hc⟩))⁻¹ * (ψ v)⁻¹ := by rw [← hC]
      _ = c * (ψ (ℓ ⟨c, hc⟩) * ψ v) * (ψ (ℓ ⟨c, hc⟩))⁻¹ * (ψ v)⁻¹ := by group
      _ = c * (ψ v * ψ (ℓ ⟨c, hc⟩)) * (ψ (ℓ ⟨c, hc⟩))⁻¹ * (ψ v)⁻¹ := by rw [h4]
      _ = c := by group
  have hconj : ∀ w, ∀ b ∈ Bs, ψ (ν w) * b * (ψ (ν w))⁻¹ ∈ Bs := by
    intro w b hb
    have hc := hcX b hb (ν w)
    have e : ψ (ν w) * b * (ψ (ν w))⁻¹ =
        b * ψ (ℓ ⟨b, hb⟩) * ψ (ν w * (ℓ ⟨b, hb⟩)⁻¹ * (ν w)⁻¹) := by
      calc ψ (ν w) * b * (ψ (ν w))⁻¹ =
          ψ (ν w) * (b * ψ (ℓ ⟨b, hb⟩)) * (ψ (ℓ ⟨b, hb⟩))⁻¹ * (ψ (ν w))⁻¹ := by group
        _ = b * ψ (ℓ ⟨b, hb⟩) * ψ (ν w) * (ψ (ℓ ⟨b, hb⟩))⁻¹ * (ψ (ν w))⁻¹ := by rw [← hc]
        _ = _ := by rw [map_mul, map_mul, map_inv, map_inv]; group
    rw [e]
    exact mul_mem (mul_mem hb (hψT _ (hℓT _)))
      (hψT _ (conj_mem_diagP hF hν w (inv_mem (hℓT _))))
  have hS5 : ∀ w, ψ (ν w) ∈ Subgroup.normalizer (Bs : Set G) := fun w =>
    Subgroup.mem_normalizer_iff.mpr fun b => ⟨hconj w b, fun hb => by
      have h := hconj w⁻¹ _ hb
      rwa [map_inv, map_inv, inv_inv,
        show (ψ (ν w))⁻¹ * (ψ (ν w) * b * (ψ (ν w))⁻¹) * ψ (ν w) = b by group] at h⟩
  let ε₀ : GGWeyl (Unitary.rootDatum (card_PSUF t) 6) →* MulAut ↥Bs :=
    Bs.normalizerMonoidHom.comp ((ψ.comp ν).codRestrict _ hS5)
  have hε₀ : ∀ w (b : ↥Bs), ((ε₀ w b : ↥Bs) : G) = ψ (ν w) * b * (ψ (ν w))⁻¹ :=
    fun _ _ => rfl
  have hmem : ∀ w, ε₀ w ∈ ggAutomizer X Bs := fun w =>
    Subgroup.subset_closure ⟨ψ (ν w), by rw [← hrange]; exact ⟨ν w, rfl⟩, hS5 w, hε₀ w⟩
  let ε₁ : GGWeyl (Unitary.rootDatum (card_PSUF t) 6) →* ↥(ggAutomizer X Bs) :=
    ε₀.codRestrict _ hmem
  have hinj : Function.Injective ε₁ := by
    refine (injective_iff_map_eq_one ε₁).mpr fun w hw => ?_
    apply eq_one_of_mem_diagSubgroup hF hν
    refine mem_diagSubgroup_of_commute hF hp hp2 hpq fun s hs => ?_
    have h3 := congrArg (fun φ : ↥(ggAutomizer X Bs) =>
      (((φ : MulAut ↥Bs) ⟨ψ s, hψT s hs⟩ : ↥Bs) : G)) hw
    change ψ (ν w) * ψ s * (ψ (ν w))⁻¹ = ψ s at h3
    have h4 : ψ (ν w) * ψ s = ψ s * ψ (ν w) := by
      calc ψ (ν w) * ψ s = ψ (ν w) * ψ s * (ψ (ν w))⁻¹ * ψ (ν w) := by group
        _ = ψ s * ψ (ν w) := by rw [h3]
    exact (htrick hs h4).symm
  have hnorm : ∀ v : ↥(Unitary.SU (PSUσ t) 6), ψ v ∈ Subgroup.normalizer (Bs : Set G) →
      ∀ s ∈ diagP (PSUF t) (t + 1) p, v * s * v⁻¹ ∈ diagP (PSUF t) (t + 1) p := by
    intro v hv s hs
    have hv' : ψ (v * s * v⁻¹) ∈ Bs := by
      rw [map_mul, map_mul, map_inv]
      exact (Subgroup.mem_normalizer_iff.mp hv _).mp (hψT s hs)
    refine ⟨mem_diagSubgroup_of_commute hF hp hp2 hpq fun s' hs' => ?_, ?_⟩
    · have hc : ψ (v * s * v⁻¹) * ψ s' = ψ s' * ψ (v * s * v⁻¹) :=
        congrArg Subtype.val (isMulCommutative_iff.mp hBs.1 ⟨_, hv'⟩ ⟨_, hψT s' hs'⟩)
      exact (htrick hs' hc).symm
    · rw [conj_pow, hs.2, mul_one, mul_inv_cancel]
  have hle : ggAutomizer X Bs ≤ ε₀.range := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro φ ⟨g, hgX, hgN, hφg⟩
    rw [← hrange] at hgX
    obtain ⟨u, rfl⟩ := hgX
    have hu' : ψ u⁻¹ ∈ Subgroup.normalizer (Bs : Set G) := by
      rw [map_inv]
      exact inv_mem hgN
    obtain ⟨h, hh, w, rfl⟩ := exists_eq_mul_of_normalizes hF hν hp hp2 hpq (hnorm u hgN)
      fun s hs => by simpa using hnorm u⁻¹ hu' s hs
    refine ⟨w, MulEquiv.ext fun b => Subtype.ext ?_⟩
    rw [hε₀, hφg, map_mul]
    have hc := hdiagC h hh _ (hconj w b b.2)
    calc ψ (ν w) * b * (ψ (ν w))⁻¹ = ψ h * (ψ (ν w) * b * (ψ (ν w))⁻¹) * (ψ h)⁻¹ := by
          rw [← hc]
          group
      _ = ψ h * ψ (ν w) * b * (ψ h * ψ (ν w))⁻¹ := by group
  have hsurj : Function.Surjective ε₁ := by
    rintro ⟨φ, hφ⟩
    obtain ⟨w, hw⟩ := hle hφ
    exact ⟨w, Subtype.ext hw⟩
  let ε := MulEquiv.ofBijective ε₁ ⟨hinj, hsurj⟩
  have hε : ∀ w (b : ↥Bs), (((ε w : MulAut ↥Bs) b : ↥Bs) : G) = ψ (ν w) * b * (ψ (ν w))⁻¹ :=
    fun _ _ => rfl
  have hT : ℓ.range = diagP (PSUF t) (t + 1) p := by
    refine Subgroup.eq_of_le_of_card_ge (by rintro _ ⟨b, rfl⟩; exact hℓT b) ?_
    exact (card_range_le_of_isDiag hp.pos (diagP (PSUF t) (t + 1) p)
      (fun x hx => mem_diagSubgroup_iff_isDiag.mp hx.1) (fun x hx => hx.2)).trans hrank
  refine ⟨ε, fun i => ⟨?_, ?_⟩, fun w i => ?_⟩
  ·
    have hsq : ((coxeterMatrix (Unitary.rootDatum (card_PSUF t) 6).isFiniteType).simple i) ^ 2 =
        1 := by
      rw [← CoxeterMatrix.toCoxeterSystem_simple]
      exact CoxeterSystem.simple_sq _ i
    rw [← Subgroup.coe_pow, ← map_pow, hsq, map_one, Subgroup.coe_one]
  ·
    let n := ν ((coxeterMatrix (Unitary.rootDatum (card_PSUF t) 6).isFiniteType).simple i)
    let ℓ' : ↥Bs →* ↥(diagP (PSUF t) (t + 1) p) := ℓ.codRestrict _ hℓT
    have hℓ' : Function.Surjective ℓ' := by
      rintro ⟨x, hx⟩
      rw [← hT] at hx
      obtain ⟨b, rfl⟩ := hx
      exact ⟨b, rfl⟩
    let χ := diagRatio (PSUF t) (t + 1) p (lowIdx i) (levelPerm i (lowIdx i))
    let β := χ.comp ℓ'
    have hfix : ∀ c : ↥Bs, (ε ((coxeterMatrix
        (Unitary.rootDatum (card_PSUF t) 6).isFiniteType).simple i) : MulAut ↥Bs) c = c ↔
        c ∈ β.ker := by
      intro c
      rw [MonoidHom.mem_ker]
      change _ ↔ χ ⟨ℓ c, hℓT c⟩ = 1
      rw [← mem_diagFix_simple_iff_diagRatio hν hpq i ⟨ℓ c, hℓT c⟩, mem_diagFix]
      constructor
      · intro h
        have h1 : ψ n * c * (ψ n)⁻¹ = c := congrArg Subtype.val h
        have h2 : (c : G) * ψ n = ψ n * c := by
          calc (c : G) * ψ n = ψ n * c * (ψ n)⁻¹ * ψ n := by rw [h1]
            _ = ψ n * c := by group
        refine ⟨hℓT c, (htrick (hℓT c) (hlift c c.2 n h2)).symm⟩
      · rintro ⟨-, h⟩
        apply Subtype.ext
        refine hunlift c c.2 n ?_
        change ψ (ℓ c) * ψ n = ψ n * ψ (ℓ c)
        rw [← map_mul, h, map_mul]
    have hcard1 : Nat.card {c : ↥Bs // (ε ((coxeterMatrix
        (Unitary.rootDatum (card_PSUF t) 6).isFiniteType).simple i) : MulAut ↥Bs) c = c} =
        Nat.card β.ker :=
      Nat.card_congr (Equiv.subtypeEquivRight hfix)
    have hrβ : β.range = χ.range := by
      rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr hℓ', ← MonoidHom.range_eq_map]
    rw [hcard1, ← card_range_diagRatio_simple hF hp hp2 hpq i, ← hrβ]
    exact Subgroup.card_ker_mul_card_range β
  ·
    let u := w * (coxeterMatrix (Unitary.rootDatum (card_PSUF t) 6).isFiniteType).simple i * w⁻¹
    let r : MulAut ↥Bs := ((ε u : ↥(ggAutomizer X Bs)) : MulAut ↥Bs)
    have hH : ∀ y : G, y ∈ ggHyperplane Bs r ↔ y ∈ Bs ∧ y * ψ (ν u) = ψ (ν u) * y := by
      intro y
      constructor
      · rintro ⟨b', hb', rfl⟩
        have h1 : ψ (ν u) * b' * (ψ (ν u))⁻¹ = b' := congrArg Subtype.val hb'
        refine ⟨b'.2, ?_⟩
        calc (b' : G) * ψ (ν u) = ψ (ν u) * b' * (ψ (ν u))⁻¹ * ψ (ν u) := by rw [h1]
          _ = ψ (ν u) * b' := by group
      · rintro ⟨hy, hyn⟩
        refine ⟨⟨y, hy⟩, Subtype.ext ?_, rfl⟩
        change ψ (ν u) * y * (ψ (ν u))⁻¹ = y
        rw [← hyn, mul_inv_cancel_right]
    have hXC : X ⊓ Subgroup.centralizer (ggHyperplane Bs r : Set G) =
        (Subgroup.centralizer (diagFix ν p u : Set ↥(Unitary.SU (PSUσ t) 6))).map ψ := by
      ext y
      constructor
      · rintro ⟨hyX, hyC⟩
        rw [← hrange] at hyX
        obtain ⟨z, rfl⟩ := hyX
        refine ⟨z, Subgroup.mem_centralizer_iff.mpr fun s hs => ?_, rfl⟩
        obtain ⟨hsT, hsn⟩ := mem_diagFix.mp hs
        have hψs : ψ s ∈ ggHyperplane Bs r :=
          (hH _).mpr ⟨hψT s hsT, by rw [← map_mul, hsn, map_mul]⟩
        have h1 := Subgroup.mem_centralizer_iff.mp hyC _ hψs
        exact (htrick hsT h1.symm).symm
      · rintro ⟨z, hz, rfl⟩
        refine ⟨by rw [← hrange]; exact ⟨z, rfl⟩, Subgroup.mem_centralizer_iff.mpr fun h hh => ?_⟩
        obtain ⟨hhB, hhn⟩ := (hH h).mp hh
        have h5 := htrick (hℓT ⟨h, hhB⟩) (hlift h hhB (ν u) hhn)
        have hinvE : (ℓ ⟨h, hhB⟩)⁻¹ ∈ diagFix ν p u := by
          refine mem_diagFix.mpr ⟨inv_mem (hℓT _), ?_⟩
          calc (ℓ ⟨h, hhB⟩)⁻¹ * ν u =
              (ℓ ⟨h, hhB⟩)⁻¹ * (ν u * ℓ ⟨h, hhB⟩) * (ℓ ⟨h, hhB⟩)⁻¹ := by group
            _ = (ℓ ⟨h, hhB⟩)⁻¹ * (ℓ ⟨h, hhB⟩ * ν u) * (ℓ ⟨h, hhB⟩)⁻¹ := by rw [h5]
            _ = ν u * (ℓ ⟨h, hhB⟩)⁻¹ := by group
        have hz' := Subgroup.mem_centralizer_iff.mp hz _ hinvE
        have hCz := hcX h hhB z
        calc h * ψ z = h * ψ (ℓ ⟨h, hhB⟩) * ψ ((ℓ ⟨h, hhB⟩)⁻¹ * z) := by
              rw [map_mul, map_inv]
              group
          _ = h * ψ (ℓ ⟨h, hhB⟩) * ψ (z * (ℓ ⟨h, hhB⟩)⁻¹) := by rw [hz']
          _ = h * ψ (ℓ ⟨h, hhB⟩) * ψ z * ψ ((ℓ ⟨h, hhB⟩)⁻¹) := by rw [map_mul]; group
          _ = ψ z * (h * ψ (ℓ ⟨h, hhB⟩)) * ψ ((ℓ ⟨h, hhB⟩)⁻¹) := by rw [hCz]
          _ = ψ z * h := by rw [map_inv]; group
    have hodd : Odd (Nat.card (PSUF t) - 1) := by
      rw [card_PSUF]
      exact Nat.Even.sub_odd (Nat.one_le_iff_ne_zero.mpr (by positivity))
        (Nat.even_pow.mpr ⟨Nat.even_pow.mpr ⟨even_two, by omega⟩, two_ne_zero⟩) odd_one
    rw [ggRankOneIn, hXC, ggOTwoPrime_map_of_odd_ker ψ hodd
        (fun z hz => pow_eq_one_of_mem_center hF hp hp2 hpq (hker hz)),
      ggOTwoPrime_centralizer_diagFix hν hp hp2 hpq w i]

end Chart

section Position


theorem ggKGPosSU_tableBPos_torus {G : Type} [Group G] [Finite G] {p : ℕ} {Bs X : Subgroup G}
    {f : ℕ} {ψ : (ggU .PSU 6 f).K →* G} (hloc : GGKGPosLocalHypTw p Bs X .PSU 6 f ψ) :
    ∃ ψ' : (ggU .PSU 6 f).K →* G, (∃ k, ψ' = ψ.comp (MulAut.conj k).toMonoidHom) ∧
      ψ'.ker ≤ Subgroup.center (ggU .PSU 6 f).K ∧ ψ'.range = X ∧
      GGTableBPos p Bs X .PSU 6 f ψ' ∧
      ∀ b ∈ Bs, ∃ t ∈ ggTorus (ggU .PSU 6 f).D, ∀ z, b * ψ' z * b⁻¹ = ψ' (t * z * t⁻¹) := by
  obtain ⟨t, rfl⟩ : ∃ t, f = t + 1 := ⟨f - 1, by have := hloc.1.2.2.1; omega⟩
  obtain ⟨⟨hp, hp2, -, hpq⟩, ⟨hker, hrange⟩, ⟨hBs, hN, hC3⟩, hdiag, hcard, h4⟩ := hloc
  let ψn : ↥(Unitary.SU (PSUσ t) 6) →* G := ψ
  have hdiag' : ∀ b ∈ Bs, GGPsiInnerDiag (Unitary.rootDatum (card_PSUF t) 6) ψn b := hdiag
  obtain ⟨g, ℓ, hℓ, hkerℓ, hpowℓ, hrankℓ, hdiagℓ⟩ :=
    exists_diag_lift_SU ψn hp hp2 hpq hker hrange hBs hN hdiag' hcard h4
  obtain ⟨ψ', hψ'k, hk, hr, hℓ'⟩ := exists_conj_lift ψn g ℓ hℓ
  have hker' : ψ'.ker ≤ Subgroup.center _ := hk ▸ hker
  have hrange' : ψ'.range = X := hr ▸ hrange
  have hℓT : ∀ b, ℓ b ∈ diagP (PSUF t) (t + 1) p := fun b =>
    ⟨mem_diagSubgroup_iff_isDiag.mpr (hdiagℓ b), hpowℓ b⟩
  obtain ⟨htor, hcardB⟩ := torus_card_of_diag_lift hp.pos ψ' ℓ hℓ' hkerℓ hpowℓ hdiagℓ
  have hadm : StatedLieAdmissible .PSU 6 2 (t + 1) :=
    ⟨Nat.prime_two, by omega, by norm_num, by simp⟩
  obtain ⟨ν, hν⟩ := (ggTagFacts_PSU hadm (by decide)).2.1
  obtain ⟨ε, hrefl, hrk⟩ :=
    exists_tableB_chart ψ' hp hp2 hpq hker' hrange' hBs hC3 ℓ hℓ' hℓT hrankℓ hν
  exact ⟨ψ', ⟨g⁻¹, hψ'k⟩, hker', hrange', ⟨ε, hrefl, hrk, hcardB⟩, htor⟩

theorem ggTableBPosImage_PSU_of_localHypTw {G : Type} [Group G] [Finite G] {p : ℕ}
    {Bs X : Subgroup G} {f : ℕ} {ψ : (ggU .PSU 6 f).K →* G}
    (hloc : GGKGPosLocalHypTw p Bs X .PSU 6 f ψ) : GGTableBPosImage p Bs .PSU 6 f X := by
  obtain ⟨ψ', -, hker', hrange', hpos, -⟩ := ggKGPosSU_tableBPos_torus hloc
  exact ⟨ψ', hker', hrange', hpos⟩

end Position

end CFSG.StandardType.KGPosSU

end
