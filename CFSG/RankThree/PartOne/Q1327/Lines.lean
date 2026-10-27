module

public import CFSG.RankThree.PartOne.S12.Sec1322Reflect
import CFSG.RankThree.PartOne.S9.OddCore.TorsionCommon
public import CFSG.RankThree.PartOne.S12.ReflectionFacts

public section

namespace CFSG.RankThree.PartOne.Q1327

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartOne
  CFSG.RankThree.PartOne.Torsion37

variable {G : Type} [Group G] {p : ℕ} {E : Subgroup G}

theorem mem_autMoved_iff' (hcomm : ∀ a b : E, a * b = b * a) (t : MulAut E) {x : E} :
    x ∈ autMoved E t ↔ ∃ e : E, t e * e⁻¹ = x := by
  rw [← Sec13Base.range_moveHom hcomm t]
  simp [MonoidHom.mem_range, Sec13Base.moveHom_apply]

theorem autMoved_mul_le (hcomm : ∀ x y : E, x * y = y * x) {a a' : MulAut E} (hc : a * a' = a' * a) :
    autMoved E (a * a') ≤ autMoved E a ⊔ autMoved E a' := by
  intro x hx
  obtain ⟨e, rfl⟩ := (mem_autMoved_iff' hcomm _).1 hx
  have hmul : (a * a') e = a (a' e) := rfl
  have hswap : a (a' e) = a' (a e) := by
    have := congrArg (fun m : MulAut E => m e) hc
    simpa using this
  have h1 : (a * a') e * e⁻¹ = (a' (a e) * (a e)⁻¹) * (a e * e⁻¹) := by
    rw [hmul, hswap]
    group
  rw [h1, sup_comm]
  exact Subgroup.mul_mem_sup ((mem_autMoved_iff' hcomm a').2 ⟨a e, rfl⟩)
    ((mem_autMoved_iff' hcomm a).2 ⟨e, rfl⟩)

theorem autMoved_le_of_commute [Finite G] (hd : RefFacts.ElemData p E) {u b : MulAut E}
    (huu : u * u = 1) (hbu : b * u = u * b) (hfix : ∀ f ∈ autFixed E u, b f = f) :
    autMoved E b ≤ autMoved E u := by
  have hsup := Sec13Base.fixed_sup_moved hd.comm u hd.prime hd.ne_two hd.pow huu
  have hpres : ∀ m ∈ autMoved E u, b m ∈ autMoved E u := by
    intro m hm
    obtain ⟨x, rfl⟩ := (mem_autMoved_iff' hd.comm u).1 hm
    refine (mem_autMoved_iff' hd.comm u).2 ⟨b x, ?_⟩
    have : b (u x) = u (b x) := by
      have := congrArg (fun m : MulAut E => m x) hbu
      simpa using this
    rw [map_mul, map_inv, this]
  rw [← Sec13Base.range_moveHom hd.comm b]
  rintro _ ⟨e, rfl⟩
  rw [Sec13Base.moveHom_apply]
  have he : e ∈ autFixed E u ⊔ autMoved E u := by rw [hsup]; trivial
  obtain ⟨f, hf, m, hm, hfm⟩ := exists_mul_of_mem_sup_of_commute (fun k _ l _ => hd.comm k l) he
  rw [hfm]
  have h1 : b (f * m) * (f * m)⁻¹ = b m * m⁻¹ := by
    rw [map_mul, hfix f hf, mul_inv_rev]
    calc f * b m * (m⁻¹ * f⁻¹) = f * (b m * m⁻¹) * f⁻¹ := by group
      _ = b m * m⁻¹ := by rw [hd.comm f (b m * m⁻¹)]; group
  rw [h1]
  exact Subgroup.mul_mem _ (hpres m hm) (Subgroup.inv_mem _ hm)

theorem fixes_autFixed_of_fixes_c {c : G} (hcE : c ∈ E) {u b : MulAut E}
    (hfixG : autFixedInG E u = Subgroup.zpowers c) (hbc : b ⟨c, hcE⟩ = ⟨c, hcE⟩) :
    ∀ f ∈ autFixed E u, b f = f := by
  intro f hf
  have h1 : (f : G) ∈ autFixedInG E u := ⟨f, hf, rfl⟩
  rw [hfixG] at h1
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 h1
  have hf' : f = (⟨c, hcE⟩ : E) ^ k := Subtype.ext (by simpa using hk.symm)
  rw [hf', map_zpow, hbc]

theorem E_le_of_lines [Finite G] (hd : RefFacts.ElemData p E) {c : G} (hcE : c ∈ E)
    {a a' b zs g₀ : MulAut E} (ha2 : a * a = 1) (ha'2 : a' * a' = 1) (hc : a * a' = a' * a)
    (hbu : b * (a * a') = (a * a') * b) (hbc : b ⟨c, hcE⟩ = ⟨c, hcE⟩)
    (hfixG : autFixedInG E (a * a') = Subgroup.zpowers c) (hg₀ : g₀ ∈ torusWeyl E)
    (hz : g₀ * b * g₀⁻¹ = zs) (hmov : autMovedInG E zs = Subgroup.zpowers c) {J : Subgroup G}
    (h1 : autMovedInG E a ≤ J) (h2 : autMovedInG E a' ≤ J)
    (h3 : autMovedInG E (g₀ * a * g₀⁻¹) ≤ J) (h4 : autMovedInG E (g₀ * a' * g₀⁻¹) ≤ J) :
    E ≤ J := by
  have huu : (a * a') * (a * a') = 1 := by
    calc (a * a') * (a * a') = a * (a' * a) * a' := by group
      _ = a * (a * a') * a' := by rw [← hc]
      _ = (a * a) * (a' * a') := by group
      _ = 1 := by rw [ha2, ha'2, one_mul]
  have hfix := fixes_autFixed_of_fixes_c hcE hfixG hbc
  have hMu : autMovedInG E (a * a') ≤ J := by
    refine (Subgroup.map_mono (autMoved_mul_le hd.comm hc)).trans ?_
    rw [Subgroup.map_sup]
    exact sup_le h1 h2
  have hMb : autMovedInG E b ≤ autMovedInG E (a * a') :=
    Subgroup.map_mono (autMoved_le_of_commute hd huu hbu hfix)
  obtain ⟨y₀, hy₀, hyg⟩ := Sec1322.exists_lift hg₀
  have hzy : zs = conjAut E y₀ hy₀ * b * (conjAut E y₀ hy₀)⁻¹ := by rw [hyg]; exact hz.symm
  have hMu' : autMovedInG E (a * a') ≤ autMovedInG E a ⊔ autMovedInG E a' := by
    unfold autMovedInG
    rw [← Subgroup.map_sup]
    exact Subgroup.map_mono (autMoved_mul_le hd.comm hc)
  have hconj_a : conjBy y₀ (autMovedInG E a) = autMovedInG E (g₀ * a * g₀⁻¹) := by
    rw [← hyg, Equivariance.autMovedInG_conj a hy₀]
  have hconj_a' : conjBy y₀ (autMovedInG E a') = autMovedInG E (g₀ * a' * g₀⁻¹) := by
    rw [← hyg, Equivariance.autMovedInG_conj a' hy₀]
  have hcJ : c ∈ J := by
    have hcz : c ∈ autMovedInG E zs := by rw [hmov]; exact Subgroup.mem_zpowers c
    rw [hzy, Equivariance.autMovedInG_conj b hy₀, Equivariance.mem_conjBy] at hcz
    have hcu : y₀⁻¹ * c * y₀ ∈ autMovedInG E a ⊔ autMovedInG E a' := hMu' (hMb hcz)
    have hc1 : c ∈ conjBy y₀ (autMovedInG E a ⊔ autMovedInG E a') := Equivariance.mem_conjBy.2 hcu
    have hsupc : conjBy y₀ (autMovedInG E a ⊔ autMovedInG E a') =
        conjBy y₀ (autMovedInG E a) ⊔ conjBy y₀ (autMovedInG E a') := by
      unfold conjBy
      exact Subgroup.map_sup _ _ _
    rw [hsupc, hconj_a, hconj_a'] at hc1
    exact (sup_le h3 h4) hc1
  intro e he
  have hsup := Sec13Base.fixed_sup_moved hd.comm (a * a') hd.prime hd.ne_two hd.pow huu
  have he' : (⟨e, he⟩ : ↥E) ∈ autFixed E (a * a') ⊔ autMoved E (a * a') := by rw [hsup]; trivial
  obtain ⟨f, hf, m, hm, hfm⟩ := exists_mul_of_mem_sup_of_commute (fun k _ l _ => hd.comm k l) he'
  have hfJ : (f : G) ∈ J := by
    have : (f : G) ∈ autFixedInG E (a * a') := ⟨f, hf, rfl⟩
    rw [hfixG] at this
    exact (Subgroup.zpowers_le.2 hcJ) this
  have hmJ : (m : G) ∈ J := hMu ⟨m, hm, rfl⟩
  have : e = (f : G) * (m : G) := congrArg Subtype.val hfm
  rw [this]
  exact J.mul_mem hfJ hmJ

theorem exists_moves_c [Finite G] (hd : RefFacts.ElemData p E) {c : G} (hcE : c ∈ E) (hc1 : c ≠ 1)
    {a a' b zs g₀ : MulAut E} (hb : IsAutReflection p E b) (hbc : b ⟨c, hcE⟩ = ⟨c, hcE⟩)
    (hfixG : autFixedInG E (a * a') = Subgroup.zpowers c) (hg₀ : g₀ ∈ torusWeyl E)
    (hz : g₀ * b * g₀⁻¹ = zs) (hmov : autMovedInG E zs = Subgroup.zpowers c) :
    c ∉ autFixedInG E (g₀ * a * g₀⁻¹) ∨ c ∉ autFixedInG E (g₀ * a' * g₀⁻¹) := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hfa, hfa'⟩ := hcon
  obtain ⟨y₀, hy₀, hyg⟩ := Sec1322.exists_lift hg₀
  have hfixt : ∀ t : MulAut E, c ∈ autFixedInG E t → t ⟨c, hcE⟩ = ⟨c, hcE⟩ := by
    intro t ht
    obtain ⟨m, hm, hmc⟩ := ht
    have : m = ⟨c, hcE⟩ := Subtype.ext hmc
    rw [← this]
    exact hm
  have hfu : c ∈ autFixedInG E (g₀ * (a * a') * g₀⁻¹) := by
    refine ⟨⟨c, hcE⟩, ?_, rfl⟩
    show (g₀ * (a * a') * g₀⁻¹) ⟨c, hcE⟩ = ⟨c, hcE⟩
    have e1 : g₀ * (a * a') * g₀⁻¹ = (g₀ * a * g₀⁻¹) * (g₀ * a' * g₀⁻¹) := by group
    rw [e1]
    show (g₀ * a * g₀⁻¹) ((g₀ * a' * g₀⁻¹) ⟨c, hcE⟩) = ⟨c, hcE⟩
    rw [hfixt _ hfa', hfixt _ hfa]
  rw [← hyg, Equivariance.autFixedInG_conj (a * a') hy₀, hfixG] at hfu
  have hle : Subgroup.zpowers c ≤ conjBy y₀ (Subgroup.zpowers c) := Subgroup.zpowers_le.2 hfu
  have hcard : Nat.card ↥(conjBy y₀ (Subgroup.zpowers c)) = Nat.card ↥(Subgroup.zpowers c) :=
    Subgroup.card_map_of_injective (MulAut.conj y₀).injective
  have heq : Subgroup.zpowers c = conjBy y₀ (Subgroup.zpowers c) :=
    Subgroup.eq_of_le_of_card_ge hle (le_of_eq hcard)
  have hzy : zs = conjAut E y₀ hy₀ * b * (conjAut E y₀ hy₀)⁻¹ := by rw [hyg]; exact hz.symm
  rw [hzy, Equivariance.autMovedInG_conj b hy₀] at hmov
  have hMb : autMovedInG E b = Subgroup.zpowers c := by
    rw [heq] at hmov
    exact Subgroup.map_injective (MulAut.conj y₀).injective hmov
  have hcb : c ∈ autMovedInG E b := by rw [hMb]; exact Subgroup.mem_zpowers c
  obtain ⟨m, hm, hmc⟩ := hcb
  have hm' : m = ⟨c, hcE⟩ := Subtype.ext hmc
  have hinv := RefFacts.t_apply_inv_of_mem_autMoved hd hb hm
  rw [hm', hbc] at hinv
  have h2 : (⟨c, hcE⟩ : E) ^ 2 = 1 := by
    rw [pow_two]
    exact mul_eq_one_iff_eq_inv.2 hinv
  have h3 : (⟨c, hcE⟩ : E) ^ p = 1 := hd.pow _
  have h4 : orderOf (⟨c, hcE⟩ : E) ∣ Nat.gcd 2 p :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h2) (orderOf_dvd_of_pow_eq_one h3)
  have hcop : Nat.gcd 2 p = 1 :=
    (Nat.coprime_primes Nat.prime_two hd.prime).2 (Ne.symm hd.ne_two)
  rw [hcop, Nat.dvd_one, orderOf_eq_one_iff] at h4
  exact hc1 (congrArg Subtype.val h4)

end CFSG.RankThree.PartOne.Q1327
