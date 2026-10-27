module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordDExclRestDefs
public import CFSG.LocalAnalysis.StandardType.GGKGForkRows
public import CFSG.LocalAnalysis.StandardType.GGSignedCoordConj
import CFSG.LocalAnalysis.StandardType.GGTBXDatumOfTor
import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelAut
import CFSG.LocalAnalysis.StandardType.GGNsq2QuotNorm
import CFSG.LocalAnalysis.StandardType.GGSignedCoordRefl
import TauCeti.GroupTheory.Coxeter.Geometric

public section

namespace CFSG.StandardType

open SpCoord CFSG.Assembly

theorem mem_coordProdStab_of_isRefl_of_ne_sgnAut {n p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {u : MulAut (Fin n → Multiplicative (ZMod p))} (hu : u ∈ bSignedFull n p) (hu2 : u ^ 2 = 1)
    (hfix : Nat.card {f // u f = f} * p = Nat.card (Fin n → Multiplicative (ZMod p)))
    (hne : ∀ i, u ≠ SpCoord.sgnAut i) : u ∈ coordProdStab n p := by
  rcases eq_sgnAut_or_swap_of_isRefl hp hp2 hu hu2 hfix with ⟨i, hi⟩ | ⟨a, b, hab, hi | hi⟩
  · exact absurd hi (hne i)
  · rw [hi]
    exact aPermutationFull_le_coordProdStab
      (Subgroup.subset_closure ⟨a, b, hab, rfl⟩)
  · rw [hi]
    have hδ : SpCoord.sgnAut a ∈ bSignedFull n p :=
      Subgroup.subset_closure (Or.inl ⟨a, rfl⟩)
    have hmem : SpCoord.sgnAut a * SpCoord.permAut (Equiv.swap a b) *
        (SpCoord.sgnAut a)⁻¹ ∈ (aPermutationFull n p).map
          (MulAut.conj (SpCoord.sgnAut a)).toMonoidHom :=
      Subgroup.mem_map.mpr ⟨_, Subgroup.subset_closure ⟨a, b, hab, rfl⟩, by
        change MulAut.conj (SpCoord.sgnAut a) (SpCoord.permAut (Equiv.swap a b)) =
          SpCoord.sgnAut a * SpCoord.permAut (Equiv.swap a b) * (SpCoord.sgnAut a)⁻¹
        rw [MulAut.conj_apply]⟩
    exact aPermutationFull_map_conj_le_coordProdStab hδ hmem

theorem pow_four_sgnAut_mul_of_isSignedPerm {n p : ℕ}
    {u : MulAut (Fin n → Multiplicative (ZMod p))} (hu : SpCoord.IsSignedPerm ⇑u)
    (hu2 : u ^ 2 = 1) (d : Fin n) : (SpCoord.sgnAut d * u) ^ 4 = 1 := by
  obtain ⟨π, ε, -, hε⟩ := hu
  have hu2' : u * u = 1 := by simpa [sq] using hu2
  have hmul : u * SpCoord.sgnAut (p := p) d = SpCoord.sgnAut (p := p) (π d) * u :=
    SpCoord.IsSignedPerm.mul_sgnAut hε d
  have hsq : (SpCoord.sgnAut (p := p) d * u) ^ 2 =
      SpCoord.sgnAut (p := p) d * SpCoord.sgnAut (p := p) (π d) := by
    rw [sq]
    calc (SpCoord.sgnAut (p := p) d * u) * (SpCoord.sgnAut (p := p) d * u)
        = SpCoord.sgnAut (p := p) d * (u * SpCoord.sgnAut (p := p) d) * u := by group
      _ = SpCoord.sgnAut (p := p) d * (SpCoord.sgnAut (p := p) (π d) * u) * u := by
          rw [hmul]
      _ = SpCoord.sgnAut (p := p) d * SpCoord.sgnAut (p := p) (π d) * (u * u) := by group
      _ = SpCoord.sgnAut (p := p) d * SpCoord.sgnAut (p := p) (π d) := by
          rw [hu2', mul_one]
  have hcomm : Commute (SpCoord.sgnAut (p := p) d) (SpCoord.sgnAut (p := p) (π d)) :=
    SpCoord.sgnAut_mul_comm (p := p) d (π d)
  have hs : (SpCoord.sgnAut (p := p) d * SpCoord.sgnAut (p := p) (π d)) ^ 2 = 1 := by
    rw [hcomm.mul_pow, SpCoord.sgnAut_sq, SpCoord.sgnAut_sq, mul_one]
  calc (SpCoord.sgnAut (p := p) d * u) ^ 4
      = ((SpCoord.sgnAut (p := p) d * u) ^ 2) ^ 2 := by
        rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul]
    _ = (SpCoord.sgnAut (p := p) d * SpCoord.sgnAut (p := p) (π d)) ^ 2 := by rw [hsq]
    _ = 1 := hs

private theorem dvd_four_of_map_simple_eq_sgnAut {G : Type} [Group G] {p n : ℕ} {ι : Type}
    {Bs : Subgroup G} {A : Subgroup (MulAut ↥Bs)} {M : CoxeterMatrix ι}
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p)))
    (φ : ι → MulAut ↥Bs) (hu : ∀ k, MulAut.congr eta (φ k) ∈ bSignedFull n p)
    (hu2 : ∀ k, (MulAut.congr eta (φ k)) ^ 2 = 1)
    (e : M.Group ≃* ↥A) (he : ∀ k, (e (M.simple k) : MulAut ↥Bs) = φ k)
    {k j : ι} {a : Fin n} (ha : MulAut.congr eta (φ k) = SpCoord.sgnAut a) :
    M k j ∣ 4 := by
  have hsp : SpCoord.IsSignedPerm ⇑(MulAut.congr eta (φ j)) := by
    have h := hu j
    rwa [bSignedFull_eq_signedPermSubgroup] at h
  have hpow : (MulAut.congr eta (φ k) * MulAut.congr eta (φ j)) ^ 4 = 1 := by
    rw [ha]
    exact pow_four_sgnAut_mul_of_isSignedPerm hsp (hu2 j) a
  have hpow' : (φ k * φ j) ^ 4 = 1 := by
    apply (MulAut.congr eta).injective
    rw [map_pow, map_mul, map_one]
    exact hpow
  have hs4 : (M.simple k * M.simple j) ^ 4 = 1 := by
    apply e.injective
    rw [map_pow, map_one]
    apply Subtype.ext
    rw [Subgroup.coe_pow, map_mul, Subgroup.coe_mul, he k, he j, hpow']
    rfl
  exact (M.toCoxeterSystem.simple_mul_simple_pow_eq_one_iff k j 4).mp (by
    simpa only [CoxeterMatrix.toCoxeterSystem_simple] using hs4)

theorem map_le_coordProdStab_of_coxeter_noFour {G : Type} [Group G] {p n : ℕ} {ι : Type}
    (hp : p.Prime) (hp2 : p ≠ 2) {Bs : Subgroup G} {A : Subgroup (MulAut ↥Bs)}
    {M : CoxeterMatrix ι} (hM : ∀ i, ∃ j, ¬ M i j ∣ 4)
    (φ : ι → MulAut ↥Bs) (hφ : ∀ k, GGIsReflection p (φ k))
    (e : M.Group ≃* ↥A) (he : ∀ k, (e (M.simple k) : MulAut ↥Bs) = φ k)
    (hcl : A = Subgroup.closure (Set.range φ))
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p)))
    (hA : A.map (MulAut.congr eta).toMonoidHom ≤ bSignedFull n p) :
    A.map (MulAut.congr eta).toMonoidHom ≤ coordProdStab n p := by
  have hmemA : ∀ k, φ k ∈ A := by
    intro k
    rw [hcl]
    exact Subgroup.subset_closure ⟨k, rfl⟩
  have hu : ∀ k, MulAut.congr eta (φ k) ∈ bSignedFull n p := fun k =>
    hA (Subgroup.mem_map_of_mem (MulAut.congr eta).toMonoidHom (hmemA k))
  have hu2 : ∀ k, (MulAut.congr eta (φ k)) ^ 2 = 1 := by
    intro k
    rw [← map_pow, (hφ k).1, map_one]
  have hfix : ∀ k, Nat.card {f : Fin n → Multiplicative (ZMod p) //
      MulAut.congr eta (φ k) f = f} * p =
      Nat.card (Fin n → Multiplicative (ZMod p)) := by
    intro k
    rw [card_fixed_congr eta (φ k), (hφ k).2, Nat.card_congr eta.toEquiv]
  have hcases : ∀ k, MulAut.congr eta (φ k) ∈ coordProdStab n p ∨
      ∃ i : Fin n, MulAut.congr eta (φ k) = SpCoord.sgnAut i := by
    intro k
    by_cases hne : ∃ i : Fin n, MulAut.congr eta (φ k) = SpCoord.sgnAut i
    · exact Or.inr hne
    · exact Or.inl (mem_coordProdStab_of_isRefl_of_ne_sgnAut hp hp2 (hu k) (hu2 k) (hfix k)
        fun i hi => hne ⟨i, hi⟩)
  rw [hcl, MonoidHom.map_closure]
  refine (Subgroup.closure_le _).mpr ?_
  rintro _ ⟨_, ⟨k, rfl⟩, rfl⟩
  rcases hcases k with h | ⟨a, ha⟩
  · exact h
  · exfalso
    obtain ⟨j, hj⟩ := hM k
    exact hj (dvd_four_of_map_simple_eq_sgnAut eta φ hu hu2 e he ha)

theorem map_le_coordProdStab_of_weylOfType_noFour {G : Type} [Group G] {p n : ℕ} {ι : Type}
    (hp : p.Prime) (hp2 : p ≠ 2) {Bs : Subgroup G} {A : Subgroup (MulAut ↥Bs)}
    {M : CoxeterMatrix ι} (hM : ∀ i, ∃ j, ¬ M i j ∣ 4)
    (hW : GGWeylOfType p M A)
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p)))
    (hA : A.map (MulAut.congr eta).toMonoidHom ≤ bSignedFull n p) :
    A.map (MulAut.congr eta).toMonoidHom ≤ coordProdStab n p := by
  obtain ⟨e, he⟩ := hW
  let φ : ι → MulAut ↥Bs := fun i => (e (M.simple i) : MulAut ↥Bs)
  have hφ : ∀ i, GGIsReflection p (φ i) := he
  have hcl : A = Subgroup.closure (Set.range φ) := by
    apply le_antisymm
    · intro a ha
      obtain ⟨w, hw⟩ := e.surjective ⟨a, ha⟩
      have hwa : (e w).val = a := congrArg Subtype.val hw
      rw [← hwa]
      have hwmem : w ∈ Subgroup.closure (Set.range M.simple) := by
        rw [← CoxeterMatrix.toCoxeterSystem_simple]
        rw [M.toCoxeterSystem.subgroup_closure_range_simple]
        exact Subgroup.mem_top w
      refine Subgroup.closure_induction (p := fun x _ => ↑(e x) ∈ Subgroup.closure (Set.range φ))
        ?_ ?_ ?_ ?_ hwmem
      · rintro x ⟨i, rfl⟩
        exact Subgroup.subset_closure ⟨i, rfl⟩
      · rw [map_one]
        exact Subgroup.one_mem _
      · intro x y hx hy hxmem hymem
        rw [map_mul]
        exact Subgroup.mul_mem _ hxmem hymem
      · intro x hx hxmem
        rw [map_inv]
        exact Subgroup.inv_mem _ hxmem
    · rw [Subgroup.closure_le]
      rintro _ ⟨i, rfl⟩
      exact (e (M.simple i)).2
  exact map_le_coordProdStab_of_coxeter_noFour hp hp2 hM φ hφ e (fun k => rfl) hcl eta hA

theorem false_of_sgnAut_mem_map_coordProdStab {p n : ℕ} {G : Type} [Group G]
    {Bs K : Subgroup G} (hp : p.Prime) (hp2 : p ≠ 2)
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))) {r : MulAut ↥Bs}
    (hr : r ∈ ggAutomizer K Bs) {i : Fin n} (hri : MulAut.congr eta r = SpCoord.sgnAut i)
    (hle : (ggAutomizer K Bs).map (MulAut.congr eta).toMonoidHom ≤ coordProdStab n p) : False := by
  have hmem : MulAut.congr eta r ∈ (ggAutomizer K Bs).map (MulAut.congr eta).toMonoidHom :=
    Subgroup.mem_map_of_mem _ hr
  rw [hri] at hmem
  exact sgnAut_not_mem_coordProdStab hp hp2 i (hle hmem)

theorem map_ggAutomizer_le_bSignedFull_of_join {G : Type} [Group G] {p n : ℕ} {Bs L : Subgroup G}
    {𝒦 : Finset (Subgroup G)} {K : Subgroup G} (hK𝒦 : K ∈ 𝒦)
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p)))
    (hK : (ggAutomizerJoin L Bs 𝒦).map (MulAut.congr eta).toMonoidHom = bSignedFull n p) :
    (ggAutomizer K Bs).map (MulAut.congr eta).toMonoidHom ≤ bSignedFull n p := by
  rw [← hK]
  exact Subgroup.map_mono fun x hx =>
    Subgroup.mem_sup_right (Subgroup.mem_iSup_of_mem K (Subgroup.mem_iSup_of_mem hK𝒦 hx))

theorem ggNbr_weylDatum_of_row {G : Type} [Group G] [Finite G] {p m N : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {C : Matrix (Fin N) (Fin N) ℤ} {M : CoxeterMatrix (Fin N)}
    (hMC : GGIntCartan M C) (hm : Odd m) (hpm : p ∣ m)
    {Bs X : Subgroup G} (hBs : IsElemAbelian p Bs)
    (hS : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hN : Bs ≤ Subgroup.normalizer (X : Set G))
    (hTor : GGTorusTorData m N C M ↥X (ggGamma X hN).range) :
    ∃ (φ : Fin N → MulAut ↥Bs) (e : M.Group ≃* ↥(ggAutomizer X Bs)),
      (∀ k, GGIsReflection p (φ k)) ∧ (∀ k, (e (M.simple k) : MulAut ↥Bs) = φ k) ∧
        ggAutomizer X Bs = Subgroup.closure (Set.range φ) := by
  have := Fact.mk hp
  obtain ⟨w, hw⟩ := hTor
  obtain ⟨V, hVadd, hVmod, hι⟩ :=
    exists_ggLinData (p := p) (G := G) (Bs := Bs) hBs
  let : AddCommGroup V := hVadd
  let : Module (ZMod p) V := hVmod
  obtain ⟨ι⟩ := hι
  obtain ⟨hnk, hbk, α, hlin, hpair, -, -⟩ := ggTD_linearData hm hpm hBs hS hN w hw V ι
  obtain ⟨e, he⟩ := ggTD_weyl hN hw hp2 hBs hnk
  have hcl := ggTD_closure hN hw hp2 hBs hnk
  have hfx : ∀ i, α i (ι (Additive.ofMul (⟨_, hbk i⟩ : ↥Bs))) = 2 := by
    intro i
    rw [hpair i i, hMC.1 i]
    norm_num
  exact ⟨fun k => ggTDρB X Bs (ggTDnH w hnk k), e,
    fun k => ggIsReflection_of_eq_reflection hp2 ι (hfx k)
      (ggLin_eq_reflection ι (hfx k) (hlin k)), he, hcl⟩

theorem ggNbr_map_le_coordProdStab_of_tbTorRowNoFour (hT : GGTBTorAll) (hLift : GGTBTorLiftRows)
    {G : Type} [Group G] [Finite G] {p n : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J) {y : G} {K : Subgroup G} (hnb : GGNbr p B x D J y K)
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p)))
    (hAK : (ggAutomizer K Bs).map (MulAut.congr eta).toMonoidHom ≤ bSignedFull n p)
    (hlab : GGInnerDiagOnLabel GGTBTorRowNoFour p Bs K) :
    (ggAutomizer K Bs).map (MulAut.congr eta).toMonoidHom ≤ coordProdStab n p := by
  obtain ⟨hp, hBs, -, -, -⟩ := hcfg.tableB_facts
  have hp2 : p ≠ 2 := hcfg.1.2.2.2.2.2.1.2.1
  have hS : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs := hcfg.2.1.2.2.2
  have := Fact.mk hp
  obtain ⟨_lab, _r, m, N, C, M, R, _instR, θ, I, hN, hperf, hlab2, hrow, hP, hBsI, hlift,
    hTorW, -⟩ := l05nPlQ_marking_with (ggTBTorWRows_of_all hT) hLift hp2
      (P := fun _ _ N _ M => ∀ i : Fin N, ∃ j, ¬ M i j ∣ 4) hlab
  obtain ⟨hom, hpm, hWeyl, hMC⟩ := l05nPlP1_row_facts hp hp2 hlab2 hrow
  have hTB := ggTorusTBGroup_of_nbr hcfg hnb hperf θ hN hBsI hlift
  have hTor := hTorW ↥K (ggQuotHom θ) (ggGamma K hN).range hTB
  obtain ⟨φ, e, hφ, he, hcl⟩ :=
    ggNbr_weylDatum_of_row hp hp2 hMC hom hpm hBs hS hN hTor
  exact map_le_coordProdStab_of_coxeter_noFour hp hp2 hP φ hφ e he hcl eta hAK

theorem ggTBTorRowNoFour_of_e6Row {p : ℕ} {lab : LargeEvenLabel} (hp3 : p ≠ 3)
    (h : GGKGRowLabel .e6Nonsplit p lab ∨ GGKGRowLabel .twe6Split p lab) :
    GGTBTorRowNoFour p lab := by
  have hrow : GGTBTorRowAt p lab 4 (ggTorMpm p lab) 4 CartanMatrix.F₄ CoxeterMatrix.F₄ := by
    rcases h with ⟨ht, hd⟩ | ⟨ht, hd⟩
    · exact GGTBTorRowAt.relE6 hp3 (Or.inl ⟨ht, hd⟩)
    · exact GGTBTorRowAt.relE6 hp3 (Or.inr ⟨ht, hd⟩)
  refine ⟨4, ggTorMpm p lab, 4, CartanMatrix.F₄, CoxeterMatrix.F₄, hrow, fun i => ?_⟩
  fin_cases i
  · exact ⟨1, by decide⟩
  · exact ⟨0, by decide⟩
  · exact ⟨3, by decide⟩
  · exact ⟨2, by decide⟩

end CFSG.StandardType

end
