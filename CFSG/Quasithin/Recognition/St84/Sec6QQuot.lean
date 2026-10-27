module

public import CFSG.Quasithin.Recognition.St84.Sec7Setup

public section

namespace CFSG.Quasithin.St84

open SimpleGraph CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.Fan86
open scoped Pointwise commutatorElement MatrixGroups

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V} {s : ℕ}

namespace Setup

variable (X : Setup Γ G)

theorem mem_normalizer_iff_conjSub {g : G} {A : Subgroup G} :
    g ∈ Subgroup.normalizer (A : Set G) ↔ conjSub g A = A := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  rfl

private theorem conjSub_Q_of_mem_Gi {g : G} {i : ℤ} (hg : g ∈ X.Gi i) :
    conjSub g (X.Q i) = X.Q i :=
  mem_normalizer_iff_conjSub.mp
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf (G := G) 2 (X.Gi i) hg)

theorem psl2_sylow_sq_eq_one {n : ℕ} (hn : 1 ≤ n)
    (U : Sylow 2 (PSL(2, GaloisField 2 n))) {y : PSL(2, GaloisField 2 n)}
    (hy : y ∈ (U : Subgroup (PSL(2, GaloisField 2 n)))) : y ^ 2 = 1 := by
  obtain ⟨e⟩ := CFSG.BenderSuzuki.External.huppert_II_8_2_a_sylow_equiv_additive
    (F := GaloisField 2 n) (p := 2) (f := n)
    (GaloisField.card 2 n (by omega)) U
  have hchar : ∀ a : GaloisField 2 n, a + a = 0 := by
    intro a
    rw [← two_mul, show (2 : GaloisField 2 n) = 0 from CharP.cast_eq_zero _ _, zero_mul]
  set z : Multiplicative (GaloisField 2 n) := e.symm ⟨y, hy⟩ with hz
  have hz2 : z * z = 1 := by
    show Multiplicative.ofAdd (z.toAdd + z.toAdd) = 1
    rw [hchar]
    rfl
  have hyz : ((e z : ↥U) : PSL(2, GaloisField 2 n)) = y := by
    simp [hz]
  rw [← hyz]
  have hmain : ((e z : ↥U) : PSL(2, GaloisField 2 n)) ^ 2 = 1 := by
    rw [sq, ← Subgroup.coe_mul, ← map_mul, hz2, map_one]
    rfl
  exact hmain

variable {v : V} {n : ℕ} {N : Subgroup G}

private theorem eq_pointSylow_of_le_pointBorel {hN : IsLocL2 Γ G v n N}
    (hadj : ∀ (g : G) (u w : V), Γ.Adj (g • u) (g • w) ↔ Γ.Adj u w)
    (hfin : Finite (MulAction.stabilizer G v))
    (hcard : Nat.card (Γ.neighborSet v) = 2 ^ n + 1) (hn : 1 ≤ n)
    {a : V} (ha : Γ.Adj v a) {ψ : Subgroup (PSL(2, GaloisField 2 n))}
    (hψcard : Nat.card ψ = 2 ^ n) (hψle : ψ ≤ hN.pointBorel a) :
    ψ = (hN.pointSylow hadj hfin hcard hn a : Subgroup (PSL(2, GaloisField 2 n))) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hψp : IsPGroup 2 ↥ψ := IsPGroup.of_card hψcard
  have hidx : ψ.index = (2 ^ n) ^ 2 - 1 := by
    have h := Subgroup.card_mul_index ψ
    rw [hψcard, CFSG.Walter.psl2_even_card (f := n) (by omega)] at h
    exact Nat.eq_of_mul_eq_mul_left (Nat.two_pow_pos n) h
  have hnotdvd : ¬ 2 ∣ ψ.index := by
    rw [hidx, show (2 ^ n) ^ 2 = 2 ^ (2 * n) by rw [← pow_mul]; ring_nf]
    exact (Nat.Even.sub_odd Nat.one_le_two_pow (even_two.pow_of_ne_zero (by omega))
      odd_one).not_two_dvd_nat
  let Ψ : Sylow 2 (PSL(2, GaloisField 2 n)) := IsPGroup.toSylow hψp hnotdvd
  have hΨcoe : (Ψ : Subgroup (PSL(2, GaloisField 2 n))) = ψ := rfl
  have hspec := hN.pointSylow_spec hadj hfin hcard hn ha
  have hle : (Ψ : Subgroup (PSL(2, GaloisField 2 n))) ≤ Subgroup.normalizer
      ((hN.pointSylow hadj hfin hcard hn a : Sylow 2 _) :
        Set (PSL(2, GaloisField 2 n))) := by
    rw [← hspec.2]
    exact hψle
  have heq := IsLocL2.sylow_eq_of_le_normalizer (n := n) hn hle
  rw [← hΨcoe, heq]

private theorem map_subgroupOf_le_pointBorel {hN : IsLocL2 Γ G v n N} {A : Subgroup G} {a : V}
    (hAa : A ≤ MulAction.stabilizer G a) :
    (A.subgroupOf N).map hN.phi ≤ hN.pointBorel a := by
  rintro _ ⟨x, hx, rfl⟩
  exact Subgroup.mem_map_of_mem hN.phi
    (Subgroup.mem_subgroupOf.mpr ⟨x.2, hAa (Subgroup.mem_subgroupOf.mp hx)⟩)

private theorem card_map_sylow {hN : IsLocL2 Γ G v n N} {S : Subgroup G}
    (hSN : S ≤ N)
    (hker : MonoidHom.ker hN.phi = (pCoreOf 2 (MulAction.stabilizer G v)).subgroupOf N)
    (hrel : (pCoreOf 2 (MulAction.stabilizer G v)).relIndex S = 2 ^ n) :
    Nat.card ((S.subgroupOf N).map hN.phi) = 2 ^ n := by
  rw [← Subgroup.relIndex_ker, hker, Subgroup.relIndex_subgroupOf hSN]
  exact hrel

theorem L_eq_sup_of_fixes (i : ℤ) {A B : Subgroup G} {a b : V}
    (ha : Γ.Adj (X.vert i) a) (hb : Γ.Adj (X.vert i) b) (hab : a ≠ b)
    (hA : A ≤ X.L i) (hB : B ≤ X.L i)
    (hAa : A ≤ MulAction.stabilizer G a) (hBb : B ≤ MulAction.stabilizer G b)
    (hAidx : (A ⊓ X.Q i).relIndex A = 2 ^ X.n i)
    (hBidx : (B ⊓ X.Q i).relIndex B = 2 ^ X.n i) :
    X.L i = A ⊔ B ⊔ X.Q i := by
  have hNloc : IsLocL2 Γ G (X.vert i) (X.n i) (X.L i) := X.hyp.isLocL2_oTwoPrime (X.vert i)
  have hn : 1 ≤ X.n i := (X.hyp.valency (X.vert i)).1
  have hfin : Finite (MulAction.stabilizer G (X.vert i)) := X.hyp.finite_stab (X.vert i)
  have hcard : Nat.card (Γ.neighborSet (X.vert i)) = 2 ^ X.n i + 1 :=
    (X.hyp.valency (X.vert i)).2
  have hadj := X.hyp.adj_smul
  have hker : MonoidHom.ker hNloc.phi = (X.Q i).subgroupOf (X.L i) := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact hNloc.phi_ker x
  have hArel : (X.Q i).relIndex A = 2 ^ X.n i := by
    rw [← Subgroup.inf_relIndex_left (H := A) (K := X.Q i)]
    exact hAidx
  have hBrel : (X.Q i).relIndex B = 2 ^ X.n i := by
    rw [← Subgroup.inf_relIndex_left (H := B) (K := X.Q i)]
    exact hBidx
  have hψA : (A.subgroupOf (X.L i)).map hNloc.phi =
      (hNloc.pointSylow hadj hfin hcard hn a :
        Subgroup (PSL(2, GaloisField 2 (X.n i)))) :=
    eq_pointSylow_of_le_pointBorel hadj hfin hcard hn ha
      (card_map_sylow hA hker hArel) (map_subgroupOf_le_pointBorel hAa)
  have hψB : (B.subgroupOf (X.L i)).map hNloc.phi =
      (hNloc.pointSylow hadj hfin hcard hn b :
        Subgroup (PSL(2, GaloisField 2 (X.n i)))) :=
    eq_pointSylow_of_le_pointBorel hadj hfin hcard hn hb
      (card_map_sylow hB hker hBrel) (map_subgroupOf_le_pointBorel hBb)
  have hne : (hNloc.pointSylow hadj hfin hcard hn a) ≠
      (hNloc.pointSylow hadj hfin hcard hn b) := by
    intro h
    have hbij := hNloc.pointSylow_bijective hadj hfin hcard hn
    have hΔ : (⟨a, ha⟩ : hNloc.neighborAction hadj) = ⟨b, hb⟩ := hbij.1 h
    exact hab (congrArg Subtype.val hΔ)
  have hsup : (A.subgroupOf (X.L i)).map hNloc.phi ⊔
      (B.subgroupOf (X.L i)).map hNloc.phi = ⊤ := by
    rw [hψA, hψB]
    exact psl2_sylow_two_sup_eq_top hn hne
  refine le_antisymm ?_ (sup_le (sup_le hA hB)
    (le_oTwoPrime_of_isPGroup (pCoreOf_isPGroup' (X.Gi i))
      (CFSG.LieType.BorelTits.pCoreOf_le 2 (X.Gi i))))
  intro x hx
  have hmem : hNloc.phi ⟨x, hx⟩ ∈
      (A.subgroupOf (X.L i)).map hNloc.phi ⊔ (B.subgroupOf (X.L i)).map hNloc.phi := by
    rw [hsup]
    exact Subgroup.mem_top _
  rw [← Subgroup.map_sup] at hmem
  obtain ⟨y, hy, hyφ⟩ := Subgroup.mem_map.mp hmem
  have hyAB : (y : G) ∈ A ⊔ B := by
    have hsub : (A.subgroupOf (X.L i)) ⊔ (B.subgroupOf (X.L i)) =
        (A ⊔ B).subgroupOf (X.L i) :=
      (Subgroup.subgroupOf_sup hA hB).symm
    rw [hsub] at hy
    exact Subgroup.mem_subgroupOf.mp hy
  have hmemQ : x * (y : G)⁻¹ ∈ X.Q i := by
    have hNmem : x * (y : G)⁻¹ ∈ X.L i := (X.L i).mul_mem hx ((X.L i).inv_mem y.2)
    have h1 : hNloc.phi ⟨x * (y : G)⁻¹, hNmem⟩ = 1 := by
      have hmul : (⟨x * (y : G)⁻¹, hNmem⟩ : ↥(X.L i)) = ⟨x, hx⟩ * (y)⁻¹ := rfl
      rw [hmul, map_mul, map_inv, hyφ, mul_inv_cancel]
    exact (hNloc.phi_ker _).mp h1
  have hdec : x = (x * (y : G)⁻¹) * (y : G) := by group
  rw [hdec]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hmemQ) (Subgroup.mem_sup_left hyAB)

theorem Q_neg_one_inf_Q_one_le_Q_zero :
    X.Q (-1) ⊓ X.Q 1 ≤ X.Q 0 := by
  have hP : IsPGroup 2 ↥(X.Q (-1) ⊓ X.Q 1) :=
    (pCoreOf_isPGroup' (X.Gi 1)).to_le inf_le_right
  have hAG0 : X.Q (-1) ⊓ X.Q 1 ≤ X.Gi 0 :=
    (inf_le_right.trans (X.Q_le_Gi_adj 1)).trans inf_le_left
  have hb : Γ.Adj (X.vert 0) (X.vert (-1)) := by
    have h := (X.adj (-1)).symm
    rwa [show (-1 : ℤ) + 1 = 0 by norm_num] at h
  have hab : X.vert 1 ≠ X.vert (-1) := by
    intro h
    have := X.vert_injective h
    norm_num at this
  refine le_pCoreOf_of_isPGroup_fixes_two X.hyp hP hAG0 (X.adj 0) hb hab ?_ ?_
  · intro y hy
    exact MulAction.mem_stabilizer_iff.mp (X.Q_le_Gi 1 hy.2)
  · intro y hy
    exact MulAction.mem_stabilizer_iff.mp (X.Q_le_Gi (-1) hy.1)

private theorem Q_neg_one_inf_Q_one_eq_inf_inf (hA0 : X.Q (-1) ⊓ X.Q 1 ≤ X.Q 0) :
    X.Q (-1) ⊓ X.Q 1 = (X.Q 0 ⊓ X.Q 1) ⊓ (X.Q 0 ⊓ X.Q (-1)) := by
  refine le_antisymm ?_ ?_
  · intro x hx
    exact ⟨⟨hA0 hx, hx.2⟩, ⟨hA0 hx, hx.1⟩⟩
  · intro x hx
    exact ⟨hx.2.2, hx.1.2⟩

private theorem relIndex_Q_zero_inf_Q_one (hc : CharTwoStab (V := V) (G := G)) :
    (X.Q 0 ⊓ X.Q 1).relIndex (X.Q 0) = 2 ^ X.n 1 := by
  have hQ0N : X.Q 0 ≤ Subgroup.normalizer (X.Q 1 : Set G) :=
    ((X.Q_le_Gi_adj 0).trans inf_le_right).trans
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf (G := G) 2 (X.Gi 1))
  have h := CFSG.Quasithin.B6.relIndex_sup_eq_of_le_normalizer (D := X.Q 1) (T := X.Q 0) hQ0N
  have hsup : X.Q 0 ⊔ X.Q 1 = X.S := by
    rw [← X.edgeSylow_zero]
    simpa using X.sup_Q_eq_edgeSylow hc 0
  rw [hsup] at h
  have h1 : (X.Q 1).relIndex X.S = 2 ^ X.n 1 := by
    rw [← X.edgeSylow_zero]
    exact X.relIndex_Q_succ_edgeSylow 0
  rw [h1] at h
  rw [Subgroup.inf_relIndex_left (H := X.Q 0) (K := X.Q 1)]
  exact h.symm

private theorem relIndex_Q_zero_inf_Q_neg_one (hc : CharTwoStab (V := V) (G := G)) :
    (X.Q 0 ⊓ X.Q (-1)).relIndex (X.Q 0) = 2 ^ X.n 1 := by
  have hQ0N : X.Q 0 ≤ Subgroup.normalizer (X.Q (-1) : Set G) := by
    intro x hx
    exact CFSG.LieType.BorelTits.le_normalizer_pCoreOf (G := G) 2 (X.Gi (-1))
      ((X.Q_le_Gi_adj 0).trans inf_le_left hx)
  have h := CFSG.Quasithin.B6.relIndex_sup_eq_of_le_normalizer (D := X.Q (-1)) (T := X.Q 0) hQ0N
  rw [show X.Q 0 ⊔ X.Q (-1) = X.edgeSylow (-1) from by
    rw [sup_comm]
    simpa using X.sup_Q_eq_edgeSylow hc (-1)] at h
  have h1 : (X.Q (-1)).relIndex (X.edgeSylow (-1)) = 2 ^ X.n 1 := by
    rw [X.relIndex_Q_edgeSylow (-1), X.n_neg_one]
  rw [h1] at h
  rw [Subgroup.inf_relIndex_left (H := X.Q 0) (K := X.Q (-1))]
  exact h.symm

private theorem relIndex_Q_one_inf_Q_zero (hc : CharTwoStab (V := V) (G := G)) :
    (X.Q 1 ⊓ X.Q 0).relIndex (X.Q 1) = 2 ^ X.n 0 := by
  have hQ1N : X.Q 1 ≤ Subgroup.normalizer (X.Q 0 : Set G) :=
    ((X.Q_le_Gi_adj 1).trans inf_le_left).trans
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf (G := G) 2 (X.Gi 0))
  have h := CFSG.Quasithin.B6.relIndex_sup_eq_of_le_normalizer (D := X.Q 0) (T := X.Q 1) hQ1N
  have hsup : X.Q 1 ⊔ X.Q 0 = X.S := by
    rw [sup_comm, ← X.edgeSylow_zero]
    simpa using X.sup_Q_eq_edgeSylow hc 0
  rw [hsup] at h
  have h1 : (X.Q 0).relIndex X.S = 2 ^ X.n 0 := by
    rw [← X.edgeSylow_zero]
    exact X.relIndex_Q_edgeSylow 0
  rw [h1] at h
  rw [Subgroup.inf_relIndex_left (H := X.Q 1) (K := X.Q 0)]
  exact h.symm

private theorem relIndex_Q_neg_one_inf_Q_zero (hc : CharTwoStab (V := V) (G := G)) :
    (X.Q (-1) ⊓ X.Q 0).relIndex (X.Q (-1)) = 2 ^ X.n 0 := by
  have hQmN : X.Q (-1) ≤ Subgroup.normalizer (X.Q 0 : Set G) := by
    intro x hx
    exact CFSG.LieType.BorelTits.le_normalizer_pCoreOf (G := G) 2 (X.Gi 0)
      ((X.Q_le_Gi_adj (-1)).trans inf_le_right hx)
  have h := CFSG.Quasithin.B6.relIndex_sup_eq_of_le_normalizer (D := X.Q 0) (T := X.Q (-1)) hQmN
  rw [show X.Q (-1) ⊔ X.Q 0 = X.edgeSylow (-1) from by
    simpa using X.sup_Q_eq_edgeSylow hc (-1)] at h
  have h1 : (X.Q 0).relIndex (X.edgeSylow (-1)) = 2 ^ X.n 0 := by
    simpa using X.relIndex_Q_succ_edgeSylow (-1)
  rw [h1] at h
  rw [Subgroup.inf_relIndex_left (H := X.Q (-1)) (K := X.Q 0)]
  exact h.symm

private theorem Q_zero_le_normalizer_inf_neg_one :
    X.Q 0 ≤ Subgroup.normalizer ((X.Q 0 ⊓ X.Q (-1) : Subgroup G) : Set G) := by
  have h1 : X.Q 0 ≤ Subgroup.normalizer (X.Q (-1) : Set G) := by
    intro x hx
    exact CFSG.LieType.BorelTits.le_normalizer_pCoreOf (G := G) 2 (X.Gi (-1))
      ((X.Q_le_Gi_adj 0).trans inf_le_left hx)
  intro q hq
  refine mem_normalizer_iff_conjSub.mpr ?_
  rw [conjSub_inf, conjSub_eq_of_mem (H := X.Q 0) hq, mem_normalizer_iff_conjSub.mp (h1 hq)]

theorem pCoreOf_arcStab_neg_one_two_le_Q_zero_inf_Q_one :
    pCoreOf 2 (X.arcStab (-1) 2) ≤ X.Q 0 ⊓ X.Q 1 := by
  set R : Subgroup G := pCoreOf 2 (X.arcStab (-1) 2) with hR
  have hRp : IsPGroup 2 ↥R := pCoreOf_isPGroup' (X.arcStab (-1) 2)
  have hRle : R ≤ X.arcStab (-1) 2 :=
    CFSG.LieType.BorelTits.pCoreOf_le 2 (X.arcStab (-1) 2)
  have hRGm1 : R ≤ X.Gi (-1) :=
    hRle.trans (X.arcStab_le_Gi_of_between le_rfl (by norm_num))
  have hRG0 : R ≤ X.Gi 0 :=
    hRle.trans (X.arcStab_le_Gi_of_between (by norm_num) (by norm_num))
  have hRG1 : R ≤ X.Gi 1 :=
    hRle.trans (X.arcStab_le_Gi_of_between (by norm_num) (by norm_num))
  have hRG2 : R ≤ X.Gi 2 :=
    hRle.trans (X.arcStab_le_Gi_of_between (by norm_num) le_rfl)
  have hab : X.vert 1 ≠ X.vert (-1) := by
    intro h; have := X.vert_injective h; norm_num at this
  have hb : Γ.Adj (X.vert 0) (X.vert (-1)) := by
    have h := (X.adj (-1)).symm
    rwa [show (-1 : ℤ) + 1 = 0 by norm_num] at h
  have hRleQ0 : R ≤ X.Q 0 :=
    le_pCoreOf_of_isPGroup_fixes_two X.hyp hRp hRG0 (X.adj 0) hb hab
      (fun y hy => MulAction.mem_stabilizer_iff.mp (by simpa using hRG1 hy))
      (fun y hy => MulAction.mem_stabilizer_iff.mp (by simpa using hRGm1 hy))
  have hRleQ1 : R ≤ X.Q 1 :=
    le_pCoreOf_of_isPGroup_fixes_two X.hyp hRp hRG1 (X.adj 1) (X.adj 0).symm
      (by intro h; have := X.vert_injective h; norm_num at this)
      (fun y hy => MulAction.mem_stabilizer_iff.mp (by simpa using hRG2 hy))
      (fun y hy => MulAction.mem_stabilizer_iff.mp (by simpa using hRG0 hy))
  exact le_inf hRleQ0 hRleQ1

private theorem arcStab_neg_one_two_le_Gi_neg_two
    (hEq : X.Q 0 ⊓ X.Q 1 = X.Q (-1) ⊓ X.Q 1) :
    X.arcStab (-1) 2 ≤ X.Gi (-2) := by
  have hKA' : X.K ≤ X.arcStab (-1) 2 := X.K_le_GT.trans (X.GT_le_arcStab (-1) 2)
  have hA'Gi : X.arcStab (-1) 2 ≤ X.Gi (-1) ⊓ X.Gi 0 :=
    le_inf (X.arcStab_le_Gi_of_between (by norm_num) (by norm_num))
      (X.arcStab_le_Gi_of_between (by norm_num) (by norm_num))
  obtain ⟨-, hA'sup⟩ := X.pCoreOf_eq_inf_edgeSylow (-1) hKA' (by simpa using hA'Gi)
  have hRleQ1' : pCoreOf 2 (X.arcStab (-1) 2) ≤ X.Q 0 ⊓ X.Q 1 :=
    pCoreOf_arcStab_neg_one_two_le_Q_zero_inf_Q_one X
  have hRleQm : pCoreOf 2 (X.arcStab (-1) 2) ≤ X.Q (-1) := by
    rw [hEq] at hRleQ1'
    exact hRleQ1'.trans inf_le_left
  have hRleGm2 : pCoreOf 2 (X.arcStab (-1) 2) ≤ X.Gi (-2) := by
    intro r hr
    have h := X.Q_fixes_neighbors_vert (-1) (X.vert (-2)) ?_ r (hRleQm hr)
    · exact MulAction.mem_stabilizer_iff.mp h
    · have h := (X.adj (-2)).symm
      rwa [show (-2 : ℤ) + 1 = -1 by norm_num] at h
  rw [← hA'sup]
  exact sup_le (X.K_le_Gi (-2)) hRleGm2

private theorem Q_zero_inf_Q_one_ne_Q_neg_one_inf_Q_one (hs : IsSingularity Γ G s)
    (h4 : 4 ≤ s) :
    X.Q 0 ⊓ X.Q 1 ≠ X.Q (-1) ⊓ X.Q 1 := by
  intro hEq
  have hA'leGm2 : X.arcStab (-1) 2 ≤ X.Gi (-2) :=
    arcStab_neg_one_two_le_Gi_neg_two X hEq
  have hiff : LeftTransitive Γ G (X.line.arc (-1) 3).vert 0 3 ↔ X.LeftTransAt (-1) 2 := by
    have h := X.leftTransitive_arc_iff (-1) 3
    simpa using h
  have hnotL : ¬ X.LeftTransAt (-1) 2 := by
    rw [← hiff]
    intro hL
    obtain ⟨b, hbAdj, hb2, hb0⟩ := exists_adj_ne_ne (a := X.vert (-2)) (b := X.vert 0)
      (X.hyp.three_le_card (X.vert (-1)))
    have hmem2 : Γ.Adj (X.vert (-1)) (X.vert (-2)) := by
      have h := (X.adj (-2)).symm
      rwa [show (-2 : ℤ) + 1 = -1 by norm_num] at h
    have h20 : X.vert (-2) ≠ X.vert 0 := by
      intro h; have := X.vert_injective h; norm_num at this
    obtain ⟨g, hg, hgb⟩ := hL (X.vert (-2)) b hmem2 h20 hbAdj hb0
    have hgA' : g ∈ X.arcStab (-1) 2 := by
      rw [X.stabRange_arc (-1) 3] at hg
      simpa using hg
    have hgfix : g • X.vert (-2) = X.vert (-2) :=
      MulAction.mem_stabilizer_iff.mp (hA'leGm2 hgA')
    rw [hgfix] at hgb
    exact hb2 hgb.symm
  have hreg : X.LeftTransAt (-1) 2 := by
    have h := (X.trans_of_lt hs (-1) (k := 3) (by norm_num) (by omega)).1
    simpa using h
  exact hnotL hreg

private theorem eq_of_le_of_K_normalizer {W : Subgroup G}
    (hAW : X.Q (-1) ⊓ X.Q 1 ≤ W) (hWV1 : W ≤ X.Q 0 ⊓ X.Q 1)
    (hWne : W ≠ X.Q (-1) ⊓ X.Q 1) (hWK : X.K ≤ Subgroup.normalizer (W : Set G)) :
    W = X.Q 0 ⊓ X.Q 1 := by
  by_contra hne
  have hex : ∃ x ∈ X.Q 0 ⊓ X.Q 1, x ∉ W := by
    by_contra h
    push Not at h
    exact hne (le_antisymm hWV1 h)
  obtain ⟨x, hxV1, hxW⟩ := hex
  have hey : ∃ y ∈ W, y ∉ X.Q (-1) ⊓ X.Q 1 := by
    by_contra h
    push Not at h
    exact hWne (le_antisymm (fun z hz => h z hz) hAW)
  obtain ⟨y, hyW, hyA⟩ := hey
  have hQ0E : X.Q 0 ≤ X.edgeSylow (-1) := by simpa using X.Q_le_edgeSylow (-1)
  have hxE : x ∈ X.edgeSylow (-1) := hQ0E (Subgroup.mem_inf.mp hxV1).1
  have hyE : y ∈ X.edgeSylow (-1) := hQ0E (Subgroup.mem_inf.mp (hWV1 hyW)).1
  have hxQ : x ∉ X.Q (-1) := by
    intro hx
    exact hxW (hAW ⟨hx, hxV1.2⟩)
  have hyQ : y ∉ X.Q (-1) := by
    intro hy
    exact hyA ⟨hy, (hWV1 hyW).2⟩
  obtain ⟨k, hkK, hk⟩ := X.exists_conj_mem_Q_left (-1) hxE hyE hxQ hyQ
  have hkQ0 : conjSub k (X.Q 0) = X.Q 0 := conjSub_Q_of_mem_Gi X (X.K_le_Gi 0 hkK.1)
  have hkQ1 : conjSub k (X.Q 1) = X.Q 1 := conjSub_Q_of_mem_Gi X (X.K_le_Gi 1 hkK.1)
  have hkV1 : conjSub k (X.Q 0 ⊓ X.Q 1) = X.Q 0 ⊓ X.Q 1 := by
    rw [conjSub_inf, hkQ0, hkQ1]
  have hkW : conjSub k W = W := mem_normalizer_iff_conjSub.mp (hWK hkK.1)
  have hxconj : k * x * k⁻¹ ∈ X.Q 0 ⊓ X.Q 1 := by
    have h : k * x * k⁻¹ ∈ conjSub k (X.Q 0 ⊓ X.Q 1) := mul_mem_conjSub hxV1
    rwa [hkV1] at h
  have hzV1 : k * x * k⁻¹ * y⁻¹ ∈ X.Q 0 ⊓ X.Q 1 :=
    (X.Q 0 ⊓ X.Q 1).mul_mem hxconj ((X.Q 0 ⊓ X.Q 1).inv_mem (hWV1 hyW))
  have hzA : k * x * k⁻¹ * y⁻¹ ∈ X.Q (-1) ⊓ X.Q 1 := ⟨hk, hzV1.2⟩
  have hkxW : k * x * k⁻¹ ∈ W := by
    have hzW : k * x * k⁻¹ * y⁻¹ ∈ W := hAW hzA
    have h := W.mul_mem hzW hyW
    rwa [show k * x * k⁻¹ * y⁻¹ * y = k * x * k⁻¹ by group] at h
  have hxW' : x ∈ W := by
    have hk' : k⁻¹ ∈ Subgroup.normalizer (W : Set G) :=
      (Subgroup.normalizer (W : Set G)).inv_mem (hWK hkK.1)
    have hkW' : conjSub k⁻¹ W = W := mem_normalizer_iff_conjSub.mp hk'
    have h : k⁻¹ * (k * x * k⁻¹) * k ∈ conjSub k⁻¹ W := by
      simpa only [inv_inv] using mul_mem_conjSub (g := k⁻¹) hkxW
    rw [hkW'] at h
    have h5 : k⁻¹ * (k * x * k⁻¹) * k = x := by group
    rwa [h5] at h
  exact hxW hxW'

private theorem Q_zero_eq_sup_inf
    (hne : X.Q 0 ⊓ X.Q 1 ≠ X.Q (-1) ⊓ X.Q 1)
    (hA0 : X.Q (-1) ⊓ X.Q 1 ≤ X.Q 0) :
    X.Q 0 = (X.Q 0 ⊓ X.Q 1) ⊔ (X.Q 0 ⊓ X.Q (-1)) := by
  refine le_antisymm ?_ (sup_le inf_le_left inf_le_left)
  by_contra hle
  have hex : ∃ x ∈ X.Q 0, x ∉ (X.Q 0 ⊓ X.Q 1) ⊔ (X.Q 0 ⊓ X.Q (-1)) := by
    by_contra h
    push Not at h
    exact hle (fun z hz => h z hz)
  obtain ⟨x, hxQ0, hxB⟩ := hex
  have hey : ∃ y ∈ X.Q 0 ⊓ X.Q 1, y ∉ X.Q 0 ⊓ X.Q (-1) := by
    by_contra h
    push Not at h
    have h1 : X.Q 0 ⊓ X.Q 1 ≤ X.Q 0 ⊓ X.Q (-1) := fun z hz => h z hz
    apply hne
    refine le_antisymm ?_ (le_inf hA0 (inf_le_right : X.Q (-1) ⊓ X.Q 1 ≤ X.Q 1))
    intro z hz
    exact ⟨(h1 hz).2, hz.2⟩
  obtain ⟨y, hyV1, hyVM⟩ := hey
  have hV1Q0 : X.Q 0 ⊓ X.Q 1 ≤ X.Q 0 := inf_le_left
  have hQ0E : X.Q 0 ≤ X.edgeSylow (-1) := by simpa using X.Q_le_edgeSylow (-1)
  have hxE : x ∈ X.edgeSylow (-1) := hQ0E hxQ0
  have hyE : y ∈ X.edgeSylow (-1) := hQ0E (hV1Q0 hyV1)
  have hxQm : x ∉ X.Q (-1) := by
    intro hx
    exact hxB (Subgroup.mem_sup_right (Subgroup.mem_inf.mpr ⟨hxQ0, hx⟩))
  have hyQm : y ∉ X.Q (-1) := by
    intro hy
    exact hyVM (Subgroup.mem_inf.mpr ⟨hV1Q0 hyV1, hy⟩)
  obtain ⟨k, hkK, hk⟩ := X.exists_conj_mem_Q_left (-1) hxE hyE hxQm hyQm
  have hkQ0 : conjSub k (X.Q 0) = X.Q 0 := conjSub_Q_of_mem_Gi X (X.K_le_Gi 0 hkK.1)
  have hkQ1 : conjSub k (X.Q 1) = X.Q 1 := conjSub_Q_of_mem_Gi X (X.K_le_Gi 1 hkK.1)
  have hkQm : conjSub k (X.Q (-1)) = X.Q (-1) :=
    conjSub_Q_of_mem_Gi X (X.K_le_Gi (-1) hkK.1)
  have hkB : conjSub k ((X.Q 0 ⊓ X.Q 1) ⊔ (X.Q 0 ⊓ X.Q (-1))) =
      (X.Q 0 ⊓ X.Q 1) ⊔ (X.Q 0 ⊓ X.Q (-1)) := by
    rw [conjSub_sup, conjSub_inf, conjSub_inf, hkQ0, hkQ1, hkQm]
  have hkx : k * x * k⁻¹ ∈ X.Q 0 := by
    have h : k * x * k⁻¹ ∈ conjSub k (X.Q 0) := mul_mem_conjSub hxQ0
    rwa [hkQ0] at h
  have hzVM : k * x * k⁻¹ * y⁻¹ ∈ X.Q 0 ⊓ X.Q (-1) :=
    ⟨(X.Q 0).mul_mem hkx ((X.Q 0).inv_mem (hV1Q0 hyV1)), hk⟩
  have hkxB : k * x * k⁻¹ ∈ (X.Q 0 ⊓ X.Q 1) ⊔ (X.Q 0 ⊓ X.Q (-1)) := by
    have h1 : k * x * k⁻¹ * y⁻¹ * y ∈ (X.Q 0 ⊓ X.Q 1) ⊔ (X.Q 0 ⊓ X.Q (-1)) :=
      Subgroup.mul_mem _ (Subgroup.mem_sup_right hzVM) (Subgroup.mem_sup_left hyV1)
    rwa [show k * x * k⁻¹ * y⁻¹ * y = k * x * k⁻¹ by group] at h1
  have hxB' : x ∈ (X.Q 0 ⊓ X.Q 1) ⊔ (X.Q 0 ⊓ X.Q (-1)) := by
    set B : Subgroup G := (X.Q 0 ⊓ X.Q 1) ⊔ (X.Q 0 ⊓ X.Q (-1)) with hBdef
    have hk' : k⁻¹ ∈ Subgroup.normalizer (B : Set G) := by
      have h : k ∈ Subgroup.normalizer (B : Set G) := mem_normalizer_iff_conjSub.mpr hkB
      exact (Subgroup.normalizer (B : Set G)).inv_mem h
    have hkB' : conjSub k⁻¹ B = B := mem_normalizer_iff_conjSub.mp hk'
    have h3 : k⁻¹ * (k * x * k⁻¹) * k ∈ conjSub k⁻¹ B := by
      simpa only [inv_inv] using mul_mem_conjSub (g := k⁻¹) hkxB
    rw [hkB'] at h3
    have h5 : k⁻¹ * (k * x * k⁻¹) * k = x := by group
    rwa [h5] at h3
  exact hxB hxB'

private theorem Q_zero_inf_neg_one_eq_of_le_normalizer (hc : CharTwoStab (V := V) (G := G))
    (hN : X.Q 1 ≤ Subgroup.normalizer ((X.Q 0 ⊓ X.Q (-1) : Subgroup G) : Set G)) :
    X.Q 0 ⊓ X.Q (-1) = X.Q 0 ⊓ X.Q 1 := by
  set VM : Subgroup G := X.Q 0 ⊓ X.Q (-1) with hVM
  set V1 : Subgroup G := X.Q 0 ⊓ X.Q 1 with hV1
  have hVMQ0 : VM ≤ X.Q 0 := by rw [hVM]; exact inf_le_left
  have hVMQm : VM ≤ X.Q (-1) := by rw [hVM]; exact inf_le_right
  have hQ0normVM : X.Q 0 ≤ Subgroup.normalizer (VM : Set G) := by
    rw [hVM]
    exact Q_zero_le_normalizer_inf_neg_one X
  have hQmnormVM : X.Q (-1) ≤ Subgroup.normalizer (VM : Set G) := by
    intro q hq
    refine mem_normalizer_iff_conjSub.mpr ?_
    rw [hVM, conjSub_inf]
    have h1 : conjSub q (X.Q 0) = X.Q 0 :=
      conjSub_Q_of_mem_Gi X ((X.Q_le_Gi_adj (-1)).trans inf_le_right hq)
    rw [h1, conjSub_eq_of_mem hq]
  have hL : X.L 0 = X.Q 1 ⊔ X.Q (-1) ⊔ X.Q 0 := by
    refine L_eq_sup_of_fixes X (i := 0) (A := X.Q 1) (B := X.Q (-1))
      (a := X.vert 1) (b := X.vert (-1)) (X.adj 0) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · have h := (X.adj (-1)).symm
      rwa [show (-1 : ℤ) + 1 = 0 by norm_num] at h
    · intro h
      have := X.vert_injective h
      norm_num at this
    · exact le_oTwoPrime_of_isPGroup (pCoreOf_isPGroup' (X.Gi 1))
        ((X.Q_le_Gi_adj 1).trans inf_le_left)
    · exact le_oTwoPrime_of_isPGroup (pCoreOf_isPGroup' (X.Gi (-1)))
        ((X.Q_le_Gi_adj (-1)).trans inf_le_right)
    · intro y hy
      exact MulAction.mem_stabilizer_iff.mp (X.Q_le_Gi 1 hy)
    · intro y hy
      exact MulAction.mem_stabilizer_iff.mp (X.Q_le_Gi (-1) hy)
    · exact relIndex_Q_one_inf_Q_zero X hc
    · exact relIndex_Q_neg_one_inf_Q_zero X hc
  have hLN : X.L 0 ≤ Subgroup.normalizer (VM : Set G) := by
    rw [hL]
    exact sup_le (sup_le hN hQmnormVM) hQ0normVM
  obtain ⟨g, hgL, hg⟩ := (X.hyp.isLocL2_oTwoPrime (X.vert 0)).trans
    (X.vert (-1)) (X.vert 1)
    (by have h := (X.adj (-1)).symm; rwa [show (-1 : ℤ) + 1 = 0 by norm_num] at h)
    (X.adj 0)
  have hgG0 : g ∈ X.Gi 0 := X.L_le_Gi 0 hgL
  have hconjQ0 : conjSub g (X.Q 0) = X.Q 0 := conjSub_Q_of_mem_Gi X hgG0
  have hconjGm : conjSub g (X.Gi (-1)) = X.Gi 1 := by
    rw [← stabilizer_smul_eq_conjSub, hg]
  have hconjQm : conjSub g (X.Q (-1)) = X.Q 1 := by
    rw [← pCoreOf_conjSub]
    rw [hconjGm]
  have hVMfixed : conjSub g VM = VM := mem_normalizer_iff_conjSub.mp (hLN hgL)
  have hVMtoV1 : conjSub g VM = V1 := by
    rw [hVM, conjSub_inf, hconjQ0, hconjQm, hV1]
  rw [← hVMfixed, hVMtoV1]

theorem sq_mem_Q_of_relIndex {S : Subgroup G} {j : ℤ}
    (hS : S ≤ X.L j) (hrel : (X.Q j).relIndex S = 2 ^ X.n j) :
    ∀ x ∈ S, x ^ 2 ∈ X.Q j := by
  have hNloc : IsLocL2 Γ G (X.vert j) (X.n j) (X.L j) := X.hyp.isLocL2_oTwoPrime (X.vert j)
  have hn : 1 ≤ X.n j := (X.hyp.valency (X.vert j)).1
  have hker : MonoidHom.ker hNloc.phi = (X.Q j).subgroupOf (X.L j) := by
    ext y
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact hNloc.phi_ker y
  have hψcard : Nat.card ((S.subgroupOf (X.L j)).map hNloc.phi) = 2 ^ X.n j :=
    card_map_sylow hS hker hrel
  have hψp : IsPGroup 2 ↥((S.subgroupOf (X.L j)).map hNloc.phi) := IsPGroup.of_card hψcard
  obtain ⟨U, hUle⟩ := IsPGroup.exists_le_sylow hψp
  have hUcard : Nat.card ↥U = 2 ^ X.n j := psl2_sylow_two_card hn U
  have hψeqU : (S.subgroupOf (X.L j)).map hNloc.phi =
      (U : Subgroup (PSL(2, GaloisField 2 (X.n j)))) :=
    Subgroup.eq_of_le_of_card_ge hUle (by rw [hψcard]; exact hUcard.le)
  intro x hx
  have hxS : (⟨x, hS hx⟩ : ↥(X.L j)) ∈ S.subgroupOf (X.L j) := hx
  have hmemU : hNloc.phi ⟨x, hS hx⟩ ∈ (U : Subgroup (PSL(2, GaloisField 2 (X.n j)))) := by
    rw [← hψeqU]
    exact Subgroup.mem_map_of_mem hNloc.phi hxS
  have hsq : (hNloc.phi ⟨x, hS hx⟩) ^ 2 = 1 := psl2_sylow_sq_eq_one hn U hmemU
  have h1 : hNloc.phi ⟨x ^ 2, (X.L j).pow_mem (hS hx) 2⟩ = 1 := by
    have hmul : (⟨x ^ 2, (X.L j).pow_mem (hS hx) 2⟩ : ↥(X.L j)) = (⟨x, hS hx⟩) ^ 2 := rfl
    rw [hmul, map_pow, hsq]
  exact (hNloc.phi_ker _).mp h1

private theorem Q_zero_eq_inf_Q_one_sup_inf_Q_neg_one (hs : IsSingularity Γ G s)
    (h4 : 4 ≤ s) :
    X.Q 0 = (X.Q 0 ⊓ X.Q 1) ⊔ (X.Q 0 ⊓ X.Q (-1)) := by
  have hA0 : X.Q (-1) ⊓ X.Q 1 ≤ X.Q 0 := Q_neg_one_inf_Q_one_le_Q_zero X
  exact Q_zero_eq_sup_inf X (Q_zero_inf_Q_one_ne_Q_neg_one_inf_Q_one X hs h4) hA0

private theorem relIndex_Q_neg_one_inf_Q_one_Q_zero_inf_Q_one (hc : CharTwoStab (V := V) (G := G))
    (hs : IsSingularity Γ G s) (h4 : 4 ≤ s) :
    (X.Q (-1) ⊓ X.Q 1).relIndex (X.Q 0 ⊓ X.Q 1) = 2 ^ X.n 1 := by
  set V1 : Subgroup G := X.Q 0 ⊓ X.Q 1 with hV1
  set VM : Subgroup G := X.Q 0 ⊓ X.Q (-1) with hVM
  have hA0 : X.Q (-1) ⊓ X.Q 1 ≤ X.Q 0 := Q_neg_one_inf_Q_one_le_Q_zero X
  have hAinf : X.Q (-1) ⊓ X.Q 1 = V1 ⊓ VM := by
    rw [hV1, hVM]
    exact Q_neg_one_inf_Q_one_eq_inf_inf X hA0
  have hsup : X.Q 0 = V1 ⊔ VM := by
    rw [hV1, hVM]
    exact Q_zero_eq_inf_Q_one_sup_inf_Q_neg_one X hs h4
  have hV1norm : V1 ≤ Subgroup.normalizer (VM : Set G) := by
    rw [hV1, hVM]
    exact inf_le_left.trans (Q_zero_le_normalizer_inf_neg_one X)
  rw [hAinf, Subgroup.inf_relIndex_left]
  have h := CFSG.Quasithin.B6.relIndex_sup_eq_of_le_normalizer (D := VM) (T := V1) hV1norm
  rw [show V1 ⊔ VM = X.Q 0 from hsup.symm] at h
  exact h.symm.trans (relIndex_Q_zero_inf_Q_neg_one X hc)

private theorem relIndex_Q_neg_one_inf_Q_one_Q_zero (hc : CharTwoStab (V := V) (G := G))
    (hs : IsSingularity Γ G s) (h4 : 4 ≤ s) :
    (X.Q (-1) ⊓ X.Q 1).relIndex (X.Q 0) = 2 ^ (2 * X.n 1) := by
  have hA0 : X.Q (-1) ⊓ X.Q 1 ≤ X.Q 0 := Q_neg_one_inf_Q_one_le_Q_zero X
  have hA_le_V1 : X.Q (-1) ⊓ X.Q 1 ≤ X.Q 0 ⊓ X.Q 1 :=
    (Q_neg_one_inf_Q_one_eq_inf_inf X hA0).le.trans inf_le_left
  have hm := Subgroup.relIndex_mul_relIndex (H := X.Q (-1) ⊓ X.Q 1)
    (K := X.Q 0 ⊓ X.Q 1) (L := X.Q 0) hA_le_V1 inf_le_left
  rw [← hm, relIndex_Q_neg_one_inf_Q_one_Q_zero_inf_Q_one X hc hs h4,
    relIndex_Q_zero_inf_Q_one X hc, ← pow_add]
  congr 1
  ring

private theorem not_Q_one_le_normalizer_Q_zero_inf_Q_neg_one
    (hc : CharTwoStab (V := V) (G := G)) (hs : IsSingularity Γ G s) (h4 : 4 ≤ s) :
    ¬ X.Q 1 ≤ Subgroup.normalizer ((X.Q 0 ⊓ X.Q (-1) : Subgroup G) : Set G) := by
  intro hN
  have hVMV1 : X.Q 0 ⊓ X.Q (-1) = X.Q 0 ⊓ X.Q 1 :=
    Q_zero_inf_neg_one_eq_of_le_normalizer X hc hN
  have hA' : X.Q (-1) ⊓ X.Q 1 = X.Q 0 ⊓ X.Q 1 := by
    rw [Q_neg_one_inf_Q_one_eq_inf_inf X (Q_neg_one_inf_Q_one_le_Q_zero X), hVMV1, inf_idem]
  exact Q_zero_inf_Q_one_ne_Q_neg_one_inf_Q_one X hs h4 hA'.symm

private theorem commutator_inf_Q_neg_one_Q_one_le_inf_Q_one :
    ⁅X.Q 0 ⊓ X.Q (-1), X.Q 1⁆ ≤ X.Q 0 ⊓ X.Q 1 := by
  refine le_inf ?_ ?_
  · have hQ1N0 : X.Q 1 ≤ Subgroup.normalizer ((X.Q 0 : Subgroup G) : Set G) :=
      ((X.Q_le_Gi_adj 1).trans inf_le_left).trans
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf (G := G) 2 (X.Gi 0))
    exact (Subgroup.commutator_mono inf_le_left le_rfl).trans
      (Subgroup.le_normalizer_iff_commutator_le_left.mp hQ1N0)
  · rw [← Subgroup.le_normalizer_iff_commutator_le_right]
    exact inf_le_left.trans (((X.Q_le_Gi_adj 0).trans inf_le_right).trans
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf (G := G) 2 (X.Gi 1)))

private theorem K_le_normalizer_commutator_sup_inf :
    X.K ≤ Subgroup.normalizer
      ((((⁅X.Q 0 ⊓ X.Q (-1), X.Q 1⁆ ⊔ (X.Q (-1) ⊓ X.Q 1)) ⊓
        (X.Q 0 ⊓ X.Q 1) : Subgroup G) : Set G)) := by
  intro k hk
  have hkQ0 : conjSub k (X.Q 0) = X.Q 0 := conjSub_Q_of_mem_Gi X (X.K_le_Gi 0 hk)
  have hkQ1 : conjSub k (X.Q 1) = X.Q 1 := conjSub_Q_of_mem_Gi X (X.K_le_Gi 1 hk)
  have hkQm : conjSub k (X.Q (-1)) = X.Q (-1) := conjSub_Q_of_mem_Gi X (X.K_le_Gi (-1) hk)
  have hkVM : conjSub k (X.Q 0 ⊓ X.Q (-1)) = X.Q 0 ⊓ X.Q (-1) := by
    rw [conjSub_inf, hkQ0, hkQm]
  have hkA : conjSub k (X.Q (-1) ⊓ X.Q 1) = X.Q (-1) ⊓ X.Q 1 := by
    rw [conjSub_inf, hkQm, hkQ1]
  have hkV1 : conjSub k (X.Q 0 ⊓ X.Q 1) = X.Q 0 ⊓ X.Q 1 := by
    rw [conjSub_inf, hkQ0, hkQ1]
  refine mem_normalizer_iff_conjSub.mpr ?_
  rw [conjSub_inf, conjSub_sup, ← conjSub_commutator, hkVM, hkQ1, hkA, hkV1]

private theorem Q_zero_inf_Q_one_le_commutator_sup (hc : CharTwoStab (V := V) (G := G))
    (hs : IsSingularity Γ G s) (h4 : 4 ≤ s) :
    X.Q 0 ⊓ X.Q 1 ≤ ⁅X.Q 0 ⊓ X.Q (-1), X.Q 1⁆ ⊔ (X.Q (-1) ⊓ X.Q 1) := by
  have hA0 : X.Q (-1) ⊓ X.Q 1 ≤ X.Q 0 := Q_neg_one_inf_Q_one_le_Q_zero X
  have hAinf : X.Q (-1) ⊓ X.Q 1 = (X.Q 0 ⊓ X.Q 1) ⊓ (X.Q 0 ⊓ X.Q (-1)) :=
    Q_neg_one_inf_Q_one_eq_inf_inf X hA0
  have hA_le_V1 : X.Q (-1) ⊓ X.Q 1 ≤ X.Q 0 ⊓ X.Q 1 := hAinf.le.trans inf_le_left
  have hA_le_VM : X.Q (-1) ⊓ X.Q 1 ≤ X.Q 0 ⊓ X.Q (-1) := hAinf.le.trans inf_le_right
  have hcomm_ne : ¬ ⁅X.Q 0 ⊓ X.Q (-1), X.Q 1⁆ ≤ X.Q (-1) ⊓ X.Q 1 := by
    intro hle
    apply not_Q_one_le_normalizer_Q_zero_inf_Q_neg_one X hc hs h4
    rw [Subgroup.le_normalizer_iff_commutator_le_left]
    exact hle.trans hA_le_VM
  have hcomm_le_V1 : ⁅X.Q 0 ⊓ X.Q (-1), X.Q 1⁆ ≤ X.Q 0 ⊓ X.Q 1 :=
    commutator_inf_Q_neg_one_Q_one_le_inf_Q_one X
  have hWK := K_le_normalizer_commutator_sup_inf X
  have hWne : (⁅X.Q 0 ⊓ X.Q (-1), X.Q 1⁆ ⊔ (X.Q (-1) ⊓ X.Q 1)) ⊓
      (X.Q 0 ⊓ X.Q 1) ≠ X.Q (-1) ⊓ X.Q 1 := by
    intro h
    apply hcomm_ne
    have h1 : ⁅X.Q 0 ⊓ X.Q (-1), X.Q 1⁆ ≤
        (⁅X.Q 0 ⊓ X.Q (-1), X.Q 1⁆ ⊔ (X.Q (-1) ⊓ X.Q 1)) ⊓ (X.Q 0 ⊓ X.Q 1) :=
      le_inf le_sup_left hcomm_le_V1
    rw [h] at h1
    exact h1
  have hWeq : (⁅X.Q 0 ⊓ X.Q (-1), X.Q 1⁆ ⊔ (X.Q (-1) ⊓ X.Q 1)) ⊓
      (X.Q 0 ⊓ X.Q 1) = X.Q 0 ⊓ X.Q 1 :=
    eq_of_le_of_K_normalizer X
      (le_inf le_sup_right hA_le_V1)
      (inf_le_right : (⁅X.Q 0 ⊓ X.Q (-1), X.Q 1⁆ ⊔ (X.Q (-1) ⊓ X.Q 1)) ⊓
        (X.Q 0 ⊓ X.Q 1) ≤ X.Q 0 ⊓ X.Q 1)
      hWne hWK
  rw [← hWeq]
  exact inf_le_left

theorem Q_quot_of_normal_general (hc : CharTwoStab (V := V) (G := G))
    (hs : IsSingularity Γ G s) (h4 : 4 ≤ s) :
    X.Q 0 = (X.Q 0 ⊓ X.Q 1) ⊔ (X.Q 0 ⊓ X.Q (-1)) ∧
      (X.Q (-1) ⊓ X.Q 1).relIndex (X.Q 0) = 2 ^ (2 * X.n 1) ∧
      (X.Q (-1) ⊓ X.Q 1).relIndex (X.Q 0 ⊓ X.Q 1) = 2 ^ X.n 1 ∧
      ¬ (X.Q 0 ⊓ X.Q 1 ≤ Subgroup.normalizer ((X.Q 0 ⊓ X.Q (-1) : Subgroup G) : Set G) ∧
        X.Q 1 ≤ Subgroup.normalizer ((X.Q 0 ⊓ X.Q (-1) : Subgroup G) : Set G)) ∧
      X.Q 0 ⊓ X.Q 1 ≤ ⁅X.Q 0 ⊓ X.Q (-1), X.Q 1⁆ ⊔ (X.Q (-1) ⊓ X.Q 1) := by
  exact ⟨Q_zero_eq_inf_Q_one_sup_inf_Q_neg_one X hs h4,
    relIndex_Q_neg_one_inf_Q_one_Q_zero X hc hs h4,
    relIndex_Q_neg_one_inf_Q_one_Q_zero_inf_Q_one X hc hs h4,
    fun h => not_Q_one_le_normalizer_Q_zero_inf_Q_neg_one X hc hs h4 h.2,
    Q_zero_inf_Q_one_le_commutator_sup X hc hs h4⟩

end Setup

end CFSG.Quasithin.St84
