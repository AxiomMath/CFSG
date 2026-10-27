module

public import CFSG.LocalAnalysis.StandardType.GGTBTorRelDAssembly
public import CFSG.LocalAnalysis.StandardType.GGTBTorInnModel
public import CFSG.LocalAnalysis.StandardType.GGTBTorRelDMinusWeyl
public import CFSG.LocalAnalysis.StandardType.GGTBTorRelDMinusCent
public import CFSG.LocalAnalysis.StandardType.GGTableBOrthogonalEndNode
public import CFSG.LocalAnalysis.StandardType.GGOmegaMinusCentrallyClosed
public import CFSG.LocalAnalysis.StandardType.GGTBTorRel
public import CFSG.LocalAnalysis.StandardType.Marking
import CFSG.LocalAnalysis.StandardType.GGTriD4NoneMarking

public section

namespace CFSG.StandardType

namespace RelDMinus

open CFSG.Assembly TableBSymp

variable {K : Type} [Field K] [Finite K] [CharP K 2] {m p : ℕ} {b c : K}

variable (K m b c p) in
@[expose] noncomputable def primeTorus : Subgroup ↥(LargeEvenOmega (LargeEvenQMinus m b c)) :=
  ((powMonoidHom p : (Fin m → Kˣ) →* (Fin m → Kˣ)).ker).map
    (torus (K := K) (m := m) (b := b) (c := c))

theorem mem_primeTorus {g : ↥(LargeEvenOmega (LargeEvenQMinus m b c))} :
    g ∈ primeTorus K m p b c ↔ ∃ x : Fin m → Kˣ, x ^ p = 1 ∧ torus x = g := by
  simp [primeTorus, MonoidHom.mem_ker]

theorem mem_primeTorus_iff_pow {g : ↥(LargeEvenOmega (LargeEvenQMinus m b c))} :
    g ∈ primeTorus K m p b c ↔
      g ^ p = 1 ∧ g ∈ (torus (K := K) (m := m) (b := b) (c := c)).range := by
  rw [mem_primeTorus]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨by rw [← map_pow, hx, map_one], x, rfl⟩
  · rintro ⟨hg, x, rfl⟩
    exact ⟨x, torus_injective (by rw [map_pow, hg, map_one]), rfl⟩

theorem coe_mem_primeTorusGL {g : ↥(LargeEvenOmega (LargeEvenQMinus m b c))} :
    (g : GL (LargeEvenMinusIdx m) K) ∈ primeTorusGL K m p ↔ g ∈ primeTorus K m p b c := by
  rw [mem_primeTorusGL, mem_primeTorus]
  constructor
  · rintro ⟨x, hx, h⟩
    exact ⟨x, hx, Subtype.ext (by rw [coe_torus, h])⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, hx, rfl⟩

theorem commute_primeTorusGL_of_commute {g : ↥(LargeEvenOmega (LargeEvenQMinus m b c))}
    (hc : ∀ e ∈ primeTorus K m p b c, g * e = e * g) :
    ∀ e ∈ primeTorusGL K m p, (g : GL (LargeEvenMinusIdx m) K) * e = e * g := by
  intro e he
  obtain ⟨x, hx, rfl⟩ := (mem_primeTorusGL K m).mp he
  have h := congrArg Subtype.val (hc (torus x) ((mem_primeTorus).mpr ⟨x, hx, rfl⟩))
  simpa [coe_torus] using h

@[expose] noncomputable def weylElt (hm : 3 ≤ m) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (k : Fin m) : ↥(LargeEvenOmega (LargeEvenQMinus m b c)) :=
  if hk : k.val + 1 < m then swap k hk hm else sign k hm hirr

theorem torData_primeTorus {f : ℕ} (hK : Nat.card K = 2 ^ f) (hf : 1 ≤ f) (hp : p.Prime)
    (hp2 : p ≠ 2) (hpq : p ∣ Nat.card K - 1) (hm : 3 ≤ m)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    GGTorusTorData (Nat.card K - 1) m (CartanMatrix.B m) (CoxeterMatrix.B m)
      ↥(LargeEvenOmega (LargeEvenQMinus m b c)) (scalarA (primeTorus K m p b c)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hM : Odd (Nat.card K - 1) := by
    have h1 : 2 ^ f = 2 * 2 ^ (f - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    have h2 : 1 ≤ 2 ^ (f - 1) := Nat.one_le_two_pow
    exact ⟨2 ^ (f - 1) - 1, by rw [hK]; omega⟩
  have hcenter : Subgroup.center ↥(LargeEvenOmega (LargeEvenQMinus m b c)) = ⊥ := by
    have h1 := Subgroup.map_center_eq (TableBOrth.projMkEquiv
      (TableBOrth.scalars_subgroupOf_omegaMinus_eq_bot (K := K) (m := m) b c))
    rw [TableBOrth.center_omegaMinus_eq_bot hp hp2 hpq hm hirr] at h1
    exact (Subgroup.map_eq_bot_iff_of_injective _
      (f := ((TableBOrth.projMkEquiv
        (TableBOrth.scalars_subgroupOf_omegaMinus_eq_bot (K := K) (m := m) b c)) :
          ↥(LargeEvenOmega (LargeEvenQMinus m b c)) →*
            LargeEvenProj (LargeEvenOmega (LargeEvenQMinus m b c))))
      (MulEquiv.injective _)).mp h1
  have hunits : Nat.card Kˣ = Nat.card K - 1 := Nat.card_units K
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) p (by rw [hunits]; exact hpq)
  let l : Kˣ ≃* Multiplicative (ZMod (Nat.card K - 1)) :=
    (zmodCyclicMulEquiv (G := Kˣ) inferInstance).symm.trans
      (AddEquiv.toMultiplicative (ZMod.ringEquivCongr hunits).toAddEquiv)
  have hO : ∀ g : ↥(LargeEvenOmega (LargeEvenQMinus m b c)),
      (g : GL (LargeEvenMinusIdx m) K) ∈ LargeEvenOrthGroup (LargeEvenQMinus m b c) :=
    fun g => TableBOrth.omega_le_orth _ g.2
  refine RelD.ggTorusTorData_of_blockModel (M := Nat.card K - 1) hp2 hM (by omega) hcenter l
    (torus (K := K) (m := m) (b := b) (c := c)) torus_injective (primeTorus K m p b c)
    (fun g => mem_primeTorus_iff_pow) ζ hζ (weylElt hm hirr) ?_ ?_ ?_ ?_ ?_
  ·
    intro k hk x
    simp only [weylElt, dif_pos hk]
    exact swap_conj_torus k hk hm x
  ·
    intro k hk x
    have hk' : ¬ k.val + 1 < m := by omega
    simp only [weylElt, dif_neg hk']
    exact sign_conj_torus k hm hirr x
  ·
    intro g hc x
    have h := commute_torusGL_of_mem_centralizer (p := p) hp2 hζ (hO g)
      (commute_primeTorusGL_of_commute hc) x
    show torus x * g = g * torus x
    exact Subtype.ext (by simpa [coe_torus] using h.symm)
  ·
    intro g hc hpow
    obtain ⟨x, hx⟩ := eq_torusGL_of_pow_card_sub_one_eq_one (p := p) hp2 hζ hirr (hO g)
      (commute_primeTorusGL_of_commute hc)
      (by rw [← Subgroup.coe_pow, hpow, Subgroup.coe_one])
    exact ⟨x, Subtype.ext (by rw [coe_torus, hx])⟩
  ·
    intro g hg
    have hn : ∀ e ∈ primeTorusGL K m p,
        (g : GL (LargeEvenMinusIdx m) K) * e * (g : GL (LargeEvenMinusIdx m) K)⁻¹ ∈
          primeTorusGL K m p := by
      intro e he
      obtain ⟨x, hx, rfl⟩ := (mem_primeTorusGL K m).mp he
      have h : g * torus x * g⁻¹ ∈ primeTorus K m p b c :=
        (Subgroup.mem_normalizer_iff.mp hg (torus x)).mp ((mem_primeTorus).mpr ⟨x, hx, rfl⟩)
      rw [← coe_mem_primeTorusGL] at h
      simpa [coe_torus] using h
    obtain ⟨π, ε, hε, hconj⟩ := conj_torusGL_of_mem_normalizer (p := p) hp2 hζ (hO g) hn
    refine ⟨π, ε, hε, fun x hx => Subtype.ext ?_⟩
    simpa [coe_torus] using hconj x hx

theorem torData_of_elemAbelian {f : ℕ} (hK : Nat.card K = 2 ^ f) (hf : 1 ≤ f) (hp : p.Prime)
    (hp2 : p ≠ 2) (hpq : p ∣ Nat.card K - 1) (hm : 3 ≤ m)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {E : Subgroup ↥(LargeEvenOmega (LargeEvenQMinus m b c))} (hE : IsElemAbelian p E)
    (hcard : p ^ m ≤ Nat.card E) :
    GGTorusTorData (Nat.card K - 1) m (CartanMatrix.B m) (CoxeterMatrix.B m)
      ↥(LargeEvenOmega (LargeEvenQMinus m b c))
      (E.map (MulAut.conj : ↥(LargeEvenOmega (LargeEvenQMinus m b c)) →* MulAut _)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) p
    (by rw [Nat.card_units K]; exact hpq)
  have hEO : E.map (LargeEvenOmega (LargeEvenQMinus m b c)).subtype ≤ LargeEvenOrthGroup (LargeEvenQMinus m b c) := by
    rintro _ ⟨x, -, rfl⟩
    exact TableBOrth.omega_le_orth _ x.2
  obtain ⟨g, hg, χ, hχ, hs⟩ := TableBOrth.exists_orth_conj_minus (m := m) hp2 hζ hirr hEO
    (hE.map (LargeEvenOmega (LargeEvenQMinus m b c)).subtype)
    (by rw [Subgroup.card_map_of_injective (f := (LargeEvenOmega (LargeEvenQMinus m b c)).subtype) Subtype.coe_injective]; exact hcard)
  refine torData_of_conj_eq (TableBOrth.conjOmega hg) ?_
    (torData_primeTorus hK hf hp hp2 hpq hm hirr)
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    let a : ↥(E.map (LargeEvenOmega (LargeEvenQMinus m b c)).subtype) := ⟨(x : GL (LargeEvenMinusIdx m) K), x, hx, rfl⟩
    have hxp : x ^ p = 1 := hE.2 x hx
    refine (mem_primeTorus).mpr ⟨fun k => χ k a, ?_, Subtype.ext ?_⟩
    · have ha : a ^ p = 1 := by
        apply Subtype.ext
        rw [Subgroup.coe_pow, Subgroup.coe_one]
        change (x : GL (LargeEvenMinusIdx m) K) ^ p = 1
        rw [← Subgroup.coe_pow, hxp, Subgroup.coe_one]
      funext k
      rw [Pi.pow_apply, Pi.one_apply, ← map_pow, ha, map_one]
    · rw [coe_torus, torusGL_apply]
      exact (hχ a).symm
  · intro hy
    obtain ⟨z, hz, rfl⟩ := (mem_primeTorus).mp hy
    obtain ⟨a, ha⟩ := hs z (fun k => by simpa using congrFun hz k)
    obtain ⟨x, hx, hxa⟩ := a.2
    refine ⟨x, hx, Subtype.ext ?_⟩
    change g * (x : GL (LargeEvenMinusIdx m) K) * g⁻¹ =
      ((torus z : ↥(LargeEvenOmega (LargeEvenQMinus m b c))) : GL (LargeEvenMinusIdx m) K)
    rw [coe_torus, torusGL_apply]
    have h := hχ a
    rw [← hxa] at h
    simpa [ha] using h

theorem ggTorusTorW_twMinusSplit
    {f : ℕ} (hK : Nat.card K = 2 ^ f) (hf : 2 ≤ f)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card K - 1) (hm : 3 ≤ m)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    GGTorusTorW p m (Nat.card K - 1) m (CartanMatrix.B m) (CoxeterMatrix.B m)
      (OrthRest.RMinus K m b c) (LargeEvenInnSet (OrthRest.RMinus K m b c)) := by
  intro L _ _ ψ A hTB
  have hinj : Function.Injective ψ :=
    rMinus_injective_of_cover hK hf hm hirr L ψ hTB.1 hTB.2.1 hTB.2.2.1
  obtain ⟨e, -, E, hE, hEcard, -, hA⟩ := exists_innModel_of_tbGroup
    (I := LargeEvenInnSet (OrthRest.RMinus K m b c)) (fun φ ⟨x, hx⟩ => ⟨x, hx.symm⟩)
    (TableBOrth.center_omegaMinus_eq_bot hp hp2 hpq hm hirr) ψ hinj A hTB
  refine torData_of_innModel e hA ?_
  set eG := TableBOrth.projMkEquiv
    (TableBOrth.scalars_subgroupOf_omegaMinus_eq_bot (K := K) (m := m) b c)
  refine torData_of_mulEquiv_map eG.symm rfl ?_
  refine torData_of_elemAbelian hK (by omega) hp hp2 hpq hm hirr (hE.map _) ?_
  rw [Subgroup.card_map_of_injective (f := eG.symm.toMonoidHom) eG.symm.injective, hEcard]
  exact hTB.2.2.2.2.2.1

end RelDMinus

theorem largeEvenLabelAll_relD_twD_split
    {p n ℓ : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hn1 : 1 ≤ n) (hℓ : 4 ≤ ℓ) (hpn : p ∣ 2 ^ n - 1) :
    LargeEvenLabelAll ⟨.twD, ℓ, n⟩ fun R _ I _ =>
      GGTorusTorW p (ℓ - 1) (ggTorMpm p ⟨.twD, ℓ, n⟩) (ℓ - 1)
        (CartanMatrix.B (ℓ - 1)) (CoxeterMatrix.B (ℓ - 1)) R I := by
  intro Q hQ
  have h2 : ℓ ≠ 2 := by omega
  have h3 : ℓ ≠ 3 := by omega
  have hn : 2 ≤ n := by
    by_contra h
    have hn' : n = 1 := by omega
    subst hn'
    exact hp.one_lt.ne' (Nat.dvd_one.mp (by simpa using hpn))
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  simp only [h2, h3, ↓reduceIte] at hQ ⊢
  obtain ⟨K, i1, i2, hK, b, c, hirr, hQ'⟩ := hQ
  haveI : CharP K 2 := charP_two_of_card (m := n) hK
  have hM : ggTorMpm p ⟨.twD, ℓ, n⟩ = Nat.card K - 1 := by
    rw [ggTorMpm, if_pos hpn, hK]
  refine ⟨K, i1, i2, hK, b, c, hirr, hQ', ?_⟩
  rw [hM]
  exact RelDMinus.ggTorusTorW_twMinusSplit hK hn hp hp2 (by rw [hK]; exact hpn) (by omega) hirr

end CFSG.StandardType
