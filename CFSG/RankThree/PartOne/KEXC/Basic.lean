module

public import CFSG.RankThree.PartOne.S9.Planes.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.NoncyclicAbelianPGroup

public section

namespace CFSG.RankThree.PartOne.KEXC

open Subgroup CFSG
open CFSG.Assembly.RankThreeEven (localRank)

variable {G : Type*} [Group G] [Finite G]

theorem localRank_le_one_of_no_plane {p : ℕ} (hp : p.Prime)
    (h : ∀ U : Subgroup G, IsPGroup 2 U → U ≠ ⊥ → ∀ E : Subgroup G,
      E ≤ normalizer (U : Set G) → IsElementaryAbelian p E → Nat.card E = p ^ 2 → False) :
    localRank p G ≤ 1 := by
  refine csSup_le' ?_
  rintro m ⟨H', ⟨S, hS0, hS2, rfl⟩, rfl⟩
  by_contra hm
  push Not at hm
  obtain ⟨E, hEN, hE, hEc⟩ := (CFSG.RankThree.PartOne.Planes.le_pRank_iff hp
    (Subgroup.normalizer (S : Set G)) 2).1 (by omega)
  exact h S hS2 hS0 E hEN hE hEc

theorem exists_centralizing_involution {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {U E : Subgroup G}
    (hU2 : IsPGroup 2 U) (hU0 : U ≠ ⊥) (hEel : IsElementaryAbelian p E) (hEc : Nat.card E = p ^ 2)
    (hEU : E ≤ normalizer (U : Set G)) :
    ∃ e ∈ E, e ≠ 1 ∧ ∃ t ∈ U, t ≠ 1 ∧ t ^ 2 = 1 ∧ e * t = t * e := by
  have : Fact p.Prime := ⟨hp⟩
  have hEcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hEel.toIsMulCommutative.is_comm.comm (⟨x, hx⟩ : E) ⟨y, hy⟩)
  have hEexp : ∀ x ∈ E, x ^ p = 1 := fun x hx => elemPow_eq_one_of_isElementaryAbelian x hx
  let _ : MulDistribMulAction E U :=
    MulDistribMulAction.compHom U (U.normalizerMonoidHom.comp (Subgroup.inclusion hEU))
  let _ : CommGroup E := { (inferInstance : Group E) with
    mul_comm := fun a b => Subtype.ext (hEcomm a a.2 b b.2) }
  have : Fact (IsPGroup p E) := ⟨hEel.isPGroup⟩
  have hsmul : ∀ (e : E) (u : U), ((e • u : U) : G) = (e : G) * u * (e : G)⁻¹ := fun e u => rfl
  have hncyc : ¬ IsCyclic E := by
    intro hcyc
    obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := E)
    have hord : orderOf g = Nat.card E := orderOf_eq_card_of_forall_mem_zpowers hg
    have hgp : g ^ p = 1 := Subtype.ext (by simpa using hEexp g g.2)
    have h1 : Nat.card E ≤ p := hord ▸ Nat.le_of_dvd hp.pos (orderOf_dvd_of_pow_eq_one hgp)
    rw [hEc] at h1
    have := hp.two_le
    nlinarith
  have hUnt : Nontrivial U := (Subgroup.nontrivial_iff_ne_bot U).mpr hU0
  have hcop : Nat.Coprime p (Nat.card U) := by
    obtain ⟨n, -, hn⟩ := hU2.nontrivial_iff_card.mp hUnt
    rw [hn]
    exact Nat.Coprime.pow_right n ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)
  have hgen := CFSG.iSup_fixedPointSubgroup_zpowers_eq_top_of_noncyclic_abelian_pGroup_action
    (G := U) (A := E) p hcop hncyc
  obtain ⟨a, ha1, hFa⟩ : ∃ a : E, a ≠ 1 ∧ fixedPointSubgroup (↥(Subgroup.zpowers a)) U ≠ ⊥ := by
    by_contra hno
    push Not at hno
    have hbot : (⨆ (a : E) (_ : a ≠ 1), fixedPointSubgroup (↥(Subgroup.zpowers a)) U) = ⊥ := by
      refine iSup₂_eq_bot.mpr fun a ha => hno a ha
    rw [hbot] at hgen
    exact bot_ne_top hgen
  obtain ⟨vF, hvF1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hFa
  set v : U := (vF : U) with hvdef
  have hvF : v ∈ fixedPointSubgroup (↥(Subgroup.zpowers a)) U := vF.2
  have hv1 : v ≠ 1 := fun h => hvF1 (Subtype.ext h)
  have hvfix : ∀ z : Subgroup.zpowers a, ((z : E) • (v : U)) = v := by
    rw [FixedPoints.mem_subgroup] at hvF
    intro z
    exact hvF z
  have hav : (a : G) * v * (a : G)⁻¹ = v := by
    have := congrArg Subtype.val (hvfix ⟨a, Subgroup.mem_zpowers a⟩)
    rwa [hsmul] at this
  set W : Subgroup G := U ⊓ centralizer ({(a : G)} : Set G) with hW
  have hvW : ((v : U) : G) ∈ W := by
    refine ⟨v.2, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    have := hav
    rw [mul_inv_eq_iff_eq_mul] at this
    exact this.symm
  have hv1' : ((v : U) : G) ≠ 1 := fun h => hv1 (Subtype.ext h)
  have hW2 : IsPGroup 2 W := hU2.to_inf_left
  have hW0 : W ≠ ⊥ := fun h => hv1' (Subgroup.mem_bot.mp (h ▸ hvW))
  have hWnt : Nontrivial W := (Subgroup.nontrivial_iff_ne_bot W).mpr hW0
  obtain ⟨n, hn, hWn⟩ := hW2.nontrivial_iff_card.mp hWnt
  have h2W : 2 ∣ Nat.card W := by
    rw [hWn]
    exact dvd_pow_self 2 hn.ne'
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := W) 2 h2W
  have htW : (t : G) ∈ W := t.2
  have ht2 : orderOf (t : G) = 2 := by rw [Subgroup.orderOf_coe, ht]
  refine ⟨(a : G), a.2, fun h => ha1 (Subtype.ext h), (t : G), htW.1, ?_, ?_, ?_⟩
  · intro h
    rw [h, orderOf_one] at ht2
    omega
  · rw [← ht2]
    exact pow_orderOf_eq_one _
  · exact (Subgroup.mem_centralizer_singleton_iff.mp htW.2).symm

@[expose] def invCentralizer (U : Subgroup G) (e : G) : Subgroup G :=
  Subgroup.closure {x | x ∈ U ∧ x ^ 2 = 1 ∧ x * e = e * x}

omit [Finite G] in
theorem mem_invCentralizer_of {U : Subgroup G} {e x : G} (hxU : x ∈ U) (hx2 : x ^ 2 = 1)
    (hxe : x * e = e * x) : x ∈ invCentralizer U e :=
  Subgroup.subset_closure ⟨hxU, hx2, hxe⟩

omit [Finite G] in
theorem invCentralizer_le {U : Subgroup G} {e : G} : invCentralizer U e ≤ U :=
  (Subgroup.closure_le U).2 fun _ hx => hx.1

omit [Finite G] in
theorem invCentralizer_normalized {U E : Subgroup G} (hEU : E ≤ normalizer (U : Set G))
    (hEcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) {e : G} (he : e ∈ E) :
    E ≤ normalizer (invCentralizer U e : Set G) := by
  have key : ∀ g ∈ E, ∀ x ∈ invCentralizer U e, g * x * g⁻¹ ∈ invCentralizer U e := by
    intro g hg x hx
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
      obtain ⟨hyU, hy2, hye⟩ := hy
      refine mem_invCentralizer_of ?_ ?_ ?_
      · exact ((Subgroup.mem_normalizer_iff.mp (hEU hg)) y).mp hyU
      · calc (g * y * g⁻¹) ^ 2 = g * (y * y) * g⁻¹ := by rw [sq]; group
          _ = 1 := by rw [← sq, hy2]; group
      · have hge : g * e = e * g := hEcomm g hg e he
        have hge' : g⁻¹ * e = e * g⁻¹ := by
          calc g⁻¹ * e = g⁻¹ * (e * g) * g⁻¹ := by group
            _ = g⁻¹ * (g * e) * g⁻¹ := by rw [hge]
            _ = e * g⁻¹ := by group
        calc g * y * g⁻¹ * e = g * y * (g⁻¹ * e) := by group
          _ = g * y * (e * g⁻¹) := by rw [hge']
          _ = g * (y * e) * g⁻¹ := by group
          _ = g * (e * y) * g⁻¹ := by rw [hye]
          _ = e * (g * y * g⁻¹) := by
            calc g * (e * y) * g⁻¹ = (g * e) * y * g⁻¹ := by group
              _ = (e * g) * y * g⁻¹ := by rw [hge]
              _ = _ := by group
    | one => simp
    | mul x y _ _ hx hy =>
      have : g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
      rw [this]
      exact mul_mem hx hy
    | inv x _ hx =>
      have : g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ := by group
      rw [this]
      exact inv_mem hx
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact key g hg x
  · intro hx
    have := key g⁻¹ (inv_mem hg) _ hx
    simpa [mul_assoc] using this

end CFSG.RankThree.PartOne.KEXC
