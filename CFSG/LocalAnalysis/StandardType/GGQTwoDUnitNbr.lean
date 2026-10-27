module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitTorus
public import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitLayer
import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitComp
import CFSG.LocalAnalysis.StandardType.GGTypeAFarPComp
import CFSG.LocalAnalysis.StandardType.GGQTwoSU34Aux6
public import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitNbrA

public section

namespace CFSG.StandardType.QTwo

open CFSG.Assembly CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.PhanDn.QTwo
  CFSG.ClassicalInvolution.Balance.StrongBalance.Unitary
  CFSG.ClassicalInvolution.Balance.StrongBalance.Linear

variable {G : Type} [Group G] [Finite G]

theorem qtwoDB17_normalizer_of_block {Bs J N : Subgroup G} (hBsE : CFSG.Open.IsElemAbelian 3 Bs)
    (hBsJ : ∀ s ∈ Bs, J.map (MulAut.conj s).toMonoidHom = J) {y : G} (hy : y ∈ Bs)
    (hN : LargeEvenPComponent 3 (Subgroup.centralizer ({y} : Set G)) N) (hJN : J ≤ N)
    (hperf : J ≤ ⁅J, J⁆) {u : G} (hu : u ∈ J) (hu1 : u ≠ 1) (hu3 : u ^ 3 = 1) :
    Bs ≤ Subgroup.normalizer (N : Set G) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro s hs
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  have hsc : s ∈ Subgroup.centralizer ({y} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact CFSG.Open.IsElemAbelian.comm hBsE hs hy
  have hN' : LargeEvenPComponent 3 (Subgroup.centralizer ({y} : Set G))
      (N.map (MulAut.conj s).toMonoidHom) :=
    largeEvenPComponent_map_conj hN hsc
  have hJN' : J ≤ N.map (MulAut.conj s).toMonoidHom := by
    rw [← hBsJ s hs]
    exact Subgroup.map_mono hJN
  exact (eq_of_pComponents_of_perfect_common (p := 3) hN hN' hJN hJN' hperf hu hu1 hu3).symm

omit [Finite G] in
theorem qtwoDB17_inner_of_torus {Bs N X : Subgroup G} {m : ℕ} {βL : Additive ↥Bs ≃+ DVec m}
    {c : Fin m} {b' : ↥Bs} (hb' : βL (Additive.ofMul b') = Pi.single c 1)
    (htorus : ∀ t : ↥Bs, βL (Additive.ofMul t) c = 0 → (t : G) ∈ X) (hXN : X ≤ N)
    (hN : N ≤ Subgroup.centralizer ({(b' : G)} : Set G)) :
    ∀ s : ↥Bs, ∃ t ∈ N, ∀ n ∈ N, (s : G) * n * (s : G)⁻¹ = t * n * t⁻¹ := by
  intro s
  let k : ℕ := (βL (Additive.ofMul s) c).val
  let tB : ↥Bs := s * (b' ^ k)⁻¹
  have htc : βL (Additive.ofMul tB) c = 0 := by
    have hofmul : Additive.ofMul tB = Additive.ofMul s - k • Additive.ofMul b' := by
      simp only [tB, ofMul_mul, ofMul_inv, ofMul_pow, sub_eq_add_neg]
    have hβt : βL (Additive.ofMul tB) = βL (Additive.ofMul s) - k • Pi.single c 1 := by
      rw [hofmul, map_sub, map_nsmul, hb']
    rw [hβt]
    have hc : (k • Pi.single c (1 : ZMod 3) : DVec m) c = (k : ZMod 3) := by
      simp
    rw [Pi.sub_apply, hc]
    rw [show (k : ZMod 3) = βL (Additive.ofMul s) c from
      ZMod.natCast_zmod_val (βL (Additive.ofMul s) c)]
    exact sub_self _
  refine ⟨(tB : G), hXN (htorus tB htc), fun n hn => ?_⟩
  have hb'cent : (b' : G) * n = n * (b' : G) :=
    (Subgroup.mem_centralizer_singleton_iff.mp (hN hn)).symm
  have hb'k_all : ∀ j : ℕ, (b' : G) ^ j * n = n * (b' : G) ^ j := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
        rw [pow_succ]
        calc (b' : G) ^ j * (b' : G) * n = (b' : G) ^ j * ((b' : G) * n) := by group
          _ = (b' : G) ^ j * (n * (b' : G)) := by rw [hb'cent]
          _ = ((b' : G) ^ j * n) * (b' : G) := by group
          _ = (n * (b' : G) ^ j) * (b' : G) := by rw [ih]
          _ = n * ((b' : G) ^ j * (b' : G)) := by group
  have hb'k : (b' : G) ^ k * n = n * (b' : G) ^ k := hb'k_all k
  have hs_eq : (s : G) = (tB : G) * (b' : G) ^ k := by
    have : (tB : G) = (s : G) * ((b' : G) ^ k)⁻¹ := by simp [tB]
    rw [this]
    group
  calc (s : G) * n * (s : G)⁻¹
      = ((tB : G) * (b' : G) ^ k) * n * ((tB : G) * (b' : G) ^ k)⁻¹ := by rw [hs_eq]
    _ = (tB : G) * ((b' : G) ^ k * n * ((b' : G) ^ k)⁻¹) * (tB : G)⁻¹ := by group
    _ = (tB : G) * n * (tB : G)⁻¹ := by
        have : (b' : G) ^ k * n * ((b' : G) ^ k)⁻¹ = n := by rw [hb'k]; group
        rw [this]


variable {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
  {ι : Type} {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)} {m : ℕ}
  {e' : Fin m ≃ ι} {F0 : Type} [Field F0] [Finite F0] [CharP F0 2] {ψ : Su F0 2 1 m →* G}
  {ε : Equiv.Perm (Fin m) ≃* ↥(ggAutomizer L Bs)} {βL : Additive ↥Bs ≃+ DVec m} {ω : F0ˣ}
  {a b c : Fin m} {α : MulAut ↥Bs} {g : G} {b' : ↥Bs}

theorem ggQTwoDUnit_exists_N (hBal : GGLBalanceInput)
    (hEA : GGQTwoEdgeAmbientInput) (hcfg : GGQTwoDCfg p B Bs x L D J 𝒦 M e) (hm : 7 ≤ m)
    (hM : M = (ggCoxeterMatrixD m).reindex e') (hbase : QTwoUnitBase p B Bs x L ψ ε)
    (hcoords : QTwoUnitCoords Bs x L 𝒦 M e e' ψ ε βL ω) (hdel : QTwoUnitDel Bs βL a b c α g b')
    (hb'B : (b' : G) ∈ B) :
    ∃ N : Subgroup G, LargeEvenPComponent 3 (Subgroup.centralizer ({(b' : G)} : Set G)) N ∧
      qtwoDelJ ψ c ≤ N ∧ (qtwoDelJ ψ c).map (MulAut.conj g).toMonoidHom ≤ N := by
  have hBsE : CFSG.Open.IsElemAbelian p Bs := hbase.hyp.bstar.2.1
  obtain ⟨θ, hθinj, hθrange, hθrange'⟩ := ggQTwoDUnit_J_iso (by omega) hbase c g
  have hJcomp :=
    ggQTwoDUnit_J_comp hcfg (by omega) hbase hcoords hdel.hca hdel.hcb hdel.sign hdel.conj
    hdel.coord hb'B
  have hlayer := ggQTwoDUnit_layer hBal hcfg (by omega) hbase hcoords hdel.hca hdel.hcb hdel.sign
    hdel.conj hdel.coord hb'B
  have hcommon := ggQTwoDUnit_common hEA hcfg hm hM hbase hcoords hdel.hab hdel.hca hdel.hcb
    hdel.sign hdel.norm hdel.conj
  obtain ⟨hP₁, hP₂, hPperf, hP3⟩ := hcommon
  have hαb' : α b' = b' := by
    apply βL.injective
    change βL (Additive.ofMul (α b')) = βL (Additive.ofMul b')
    rw [hdel.sign b', hdel.coord]
    exact qtwoDB16_dSign_single hdel.hca hdel.hcb
  have hgb' : g * (b' : G) * g⁻¹ = (b' : G) := by
    rw [← hdel.conj b', hαb']
  have hginv : g⁻¹ * (b' : G) = (b' : G) * g⁻¹ := by
    have h : (b' : G) * g⁻¹ = g⁻¹ * (b' : G) := by
      calc (b' : G) * g⁻¹ = g⁻¹ * (g * (b' : G) * g⁻¹) := by group
        _ = g⁻¹ * (b' : G) := by rw [hgb']
    exact h.symm
  have hxH : x ∈ Subgroup.centralizer ({(b' : G)} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact CFSG.Open.IsElemAbelian.comm hBsE hbase.x_mem b'.2
  have hx'H : g * x * g⁻¹ ∈ Subgroup.centralizer ({(b' : G)} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc (g * x * g⁻¹) * (b' : G) = g * x * (g⁻¹ * (b' : G)) := by group
      _ = g * x * ((b' : G) * g⁻¹) := by rw [hginv]
      _ = g * (x * (b' : G)) * g⁻¹ := by group
      _ = g * ((b' : G) * x) * g⁻¹ := by
            rw [CFSG.Open.IsElemAbelian.comm hBsE hbase.x_mem b'.2]
      _ = (g * (b' : G) * g⁻¹) * (g * x * g⁻¹) := by group
      _ = (b' : G) * (g * x * g⁻¹) := by rw [hgb']
  have hx3 : x ^ 3 = 1 := by
    have := pow_orderOf_eq_one x
    rwa [hbase.x_order] at this
  have hx'3 : (g * x * g⁻¹) ^ 3 = 1 := by
    have hconj : (g * x * g⁻¹) ^ 3 = g * x ^ 3 * g⁻¹ := by
      rw [← MulAut.conj_apply, ← map_pow, MulAut.conj_apply]
    rw [hconj, hx3]
    group
  obtain ⟨N, hN, hJ1N, hJ2N⟩ :=
    ggQTwoDUnit_one_component (H := Subgroup.centralizer ({(b' : G)} : Set G))
      (J₁ := qtwoDelJ ψ c)
      (J₂ := (qtwoDelJ ψ c).map (MulAut.conj g).toMonoidHom)
      (P := (coordBlockSU F0 2 1 ((Finset.univ.erase c) \ {a, b})).map ψ)
      (y₁ := x) (y₂ := g * x * g⁻¹) hbase.card_field (by omega)
      ⟨θ, hθinj, hθrange⟩
      ⟨(MulAut.conj g).toMonoidHom.comp θ, (MulAut.conj g).injective.comp hθinj, hθrange'⟩
      hxH hx'H hx3 hx'3 hJcomp.1 hJcomp.2 hlayer.1 hlayer.2 hP₁ hP₂ hPperf hP3
      (fun E hE hU => by
        rw [Nat.sub_add_cancel (by omega : 1 ≤ m)]
        exact ggQTwoDUnit_rank_bound hcfg hbase E hE hU)
  exact ⟨N, hN, hJ1N, hJ2N⟩

theorem ggQTwoDUnit_normalizer_N (hm : 5 ≤ m) (hbase : QTwoUnitBase p B Bs x L ψ ε) {y : G}
    (hy : y ∈ Bs) {N : Subgroup G}
    (hN : LargeEvenPComponent 3 (Subgroup.centralizer ({y} : Set G)) N)
    (hJ₁ : qtwoDelJ ψ c ≤ N) : Bs ≤ Subgroup.normalizer (N : Set G) := by
  have hBsE : CFSG.Open.IsElemAbelian p Bs := hbase.hyp.bstar.2.1
  have hJmap : ∀ s ∈ Bs, (qtwoDelJ ψ c).map (MulAut.conj s).toMonoidHom = qtwoDelJ ψ c := by
    intro s hs
    refine le_antisymm (qtwoDB16_map_conj_J_le hbase hs) ?_
    intro z hz
    refine Subgroup.mem_map.mpr ⟨s⁻¹ * z * s, ?_, ?_⟩
    · exact qtwoDB16_map_conj_J_le hbase (Subgroup.inv_mem Bs hs)
        (Subgroup.mem_map.mpr ⟨z, hz, by
          change (MulAut.conj s⁻¹).toMonoidHom z = s⁻¹ * z * s
          simp [MulAut.conj_apply]⟩)
    · show s * (s⁻¹ * z * s) * s⁻¹ = z
      group
  obtain ⟨u, humem, hu1, hu3⟩ := qtwoDB16_J_order_three (by omega) hbase
  exact qtwoDB17_normalizer_of_block (hbase.p_eq ▸ hBsE) hJmap hy hN hJ₁
    (qtwoDB16_J_perfect (by omega) hbase) humem hu1 hu3

theorem ggQTwoDUnit_inner_N (hm : 5 ≤ m) (hbase : QTwoUnitBase p B Bs x L ψ ε)
    (hcoords : QTwoUnitCoords Bs x L 𝒦 M e e' ψ ε βL ω) (hdel : QTwoUnitDel Bs βL a b c α g b')
    {N : Subgroup G} (hN : LargeEvenPComponent 3 (Subgroup.centralizer ({(b' : G)} : Set G)) N)
    (hJ₁ : qtwoDelJ ψ c ≤ N) (hJ₂ : (qtwoDelJ ψ c).map (MulAut.conj g).toMonoidHom ≤ N) :
    ∀ s : ↥Bs, ∃ t ∈ N, ∀ n ∈ N, (s : G) * n * (s : G)⁻¹ = t * n * t⁻¹ :=
  qtwoDB17_inner_of_torus hdel.coord (ggQTwoDUnit_torus (by omega) hbase hcoords hdel.hab hdel.hca
    hdel.hcb hdel.sign hdel.norm hdel.conj) (sup_le hJ₁ hJ₂) hN.1

theorem ggQTwoDUnit_cent_E (hm : 5 ≤ m) (hbase : QTwoUnitBase p B Bs x L ψ ε)
    (hcoords : QTwoUnitCoords Bs x L 𝒦 M e e' ψ ε βL ω) (hdel : QTwoUnitDel Bs βL a b c α g b')
    (s : ↥Bs) (hs : βL (Additive.ofMul s) c = 0)
    (hs₁ : (s : G) ∈ Subgroup.centralizer (qtwoDelJ ψ c : Set G))
    (hs₂ : (s : G) ∈ Subgroup.centralizer
      ((qtwoDelJ ψ c).map (MulAut.conj g).toMonoidHom : Set G)) : s = 1 := by
  let P₁ : Submodule (ZMod 3) (DVec m) :=
    Submodule.span (ZMod 3) ({(1 : DVec m), Pi.single c 1} : Set (DVec m))
  have hxP₁ : βL (Additive.ofMul (⟨x, hbase.x_mem⟩ : ↥Bs)) ∈ P₁ := by
    rw [hcoords.x_coord hbase.x_mem]
    exact Submodule.subset_span (Set.mem_insert _ _)
  have hb'P₁ : βL (Additive.ofMul b') ∈ P₁ := by
    rw [hdel.coord]
    exact Submodule.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  have hcent1 := ggQTwoDUnit_cent_J (by omega) hbase hcoords hdel.coord
  have hsK1 : (s : G) ∈ Subgroup.closure {x, (b' : G)} := by
    rw [← hcent1]
    exact ⟨s.2, hs₁⟩
  have hβLs : βL (Additive.ofMul s) ∈ P₁ :=
    qtwoDB16_mem_span_of_mem_closure (P := P₁) hxP₁ hb'P₁ hsK1
  obtain ⟨u, v, huv⟩ :=
    (Submodule.mem_span_pair (R := ZMod 3) (x := (1 : DVec m)) (y := Pi.single c 1)).mp hβLs
  have hs'Bs : g⁻¹ * (s : G) * g ∈ Bs := by
    simpa using (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hdel.norm) (s : G)).mp s.2
  have hs'C : g⁻¹ * (s : G) * g ∈ Subgroup.centralizer (qtwoDelJ ψ c : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hgy : g * y * g⁻¹ ∈ (qtwoDelJ ψ c).map (MulAut.conj g).toMonoidHom :=
      Subgroup.mem_map.mpr ⟨y, hy, by simp⟩
    have hcomm := (Subgroup.mem_centralizer_iff.mp hs₂) (g * y * g⁻¹) hgy
    calc y * (g⁻¹ * (s : G) * g) = g⁻¹ * ((g * y * g⁻¹) * s) * g := by group
      _ = g⁻¹ * (s * (g * y * g⁻¹)) * g := by rw [hcomm]
      _ = (g⁻¹ * (s : G) * g) * y := by group
  have hs'K : g⁻¹ * (s : G) * g ∈ Subgroup.closure {x, (b' : G)} := by
    rw [← hcent1]
    exact ⟨hs'Bs, hs'C⟩
  have hβLs' : βL (Additive.ofMul (⟨g⁻¹ * (s : G) * g, hs'Bs⟩ : ↥Bs)) ∈ P₁ :=
    qtwoDB16_mem_span_of_mem_closure (P := P₁) hxP₁ hb'P₁ hs'K
  obtain ⟨u', v', huv'⟩ :=
    (Submodule.mem_span_pair (R := ZMod 3) (x := (1 : DVec m)) (y := Pi.single c 1)).mp hβLs'
  have hαs' : α (⟨g⁻¹ * (s : G) * g, hs'Bs⟩ : ↥Bs) = s := by
    apply Subtype.ext
    rw [hdel.conj (⟨g⁻¹ * (s : G) * g, hs'Bs⟩ : ↥Bs)]
    show g * (g⁻¹ * (s : G) * g) * g⁻¹ = (s : G)
    group
  have hdsign : βL (Additive.ofMul s) =
      dSign m a b (βL (Additive.ofMul (⟨g⁻¹ * (s : G) * g, hs'Bs⟩ : ↥Bs))) := by
    have h1 : βL (Additive.ofMul s) =
        βL (Additive.ofMul (α (⟨g⁻¹ * (s : G) * g, hs'Bs⟩ : ↥Bs))) := by rw [hαs']
    rw [h1, hdel.sign (⟨g⁻¹ * (s : G) * g, hs'Bs⟩ : ↥Bs)]
  have hβLs_eq : βL (Additive.ofMul s) =
      u' • dSign m a b (1 : DVec m) + v' • Pi.single c 1 := by
    rw [hdsign, ← huv']
    have h3 : dSign m a b (u' • (1 : DVec m) + v' • Pi.single c 1) =
        dSign m a b (u' • (1 : DVec m)) + dSign m a b (v' • Pi.single c 1) :=
      (dSign m a b).map_add _ _
    have h1 : dSign m a b (u' • (1 : DVec m)) = u' • dSign m a b (1 : DVec m) :=
      (dSign m a b).map_smul u' (1 : DVec m)
    have h2 : dSign m a b (v' • Pi.single c 1) = v' • dSign m a b (Pi.single c 1) :=
      (dSign m a b).map_smul v' (Pi.single c 1)
    rw [h3, h1, h2, qtwoDB16_dSign_single hdel.hca hdel.hcb]
  have hva : βL (Additive.ofMul s) a = u := by
    rw [← huv]
    simp only [Pi.add_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one]
    rw [Pi.single_eq_of_ne (M := fun _ => ZMod 3) hdel.hca.symm (1 : ZMod 3),
      mul_zero, add_zero]
  have hva' : βL (Additive.ofMul s) a = -u' := by
    rw [hβLs_eq, Pi.add_apply, Pi.smul_apply, Pi.smul_apply]
    rw [qtwoDB16_dSign_one_apply m a b a,
      Pi.single_eq_of_ne (M := fun _ => ZMod 3) hdel.hca.symm (1 : ZMod 3)]
    rw [if_pos (Or.inl rfl), smul_eq_mul, smul_zero, add_zero]
    calc u' * -1 = -(u' * 1) := mul_neg u' 1
      _ = -u' := by rw [mul_one]
  obtain ⟨kk, -, hkk⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := ({a, b, c} : Finset (Fin m))) (t := Finset.univ) (by
      rw [Finset.card_univ, Fintype.card_fin]
      have h3 := Finset.card_le_three (a := a) (b := b) (c := c)
      omega)
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hkk
  obtain ⟨hka, hkb, hkc⟩ := hkk
  have hvk : βL (Additive.ofMul s) kk = u := by
    rw [← huv]
    simp only [Pi.add_apply, Pi.smul_apply, Pi.one_apply, smul_eq_mul, mul_one]
    rw [Pi.single_eq_of_ne (M := fun _ => ZMod 3) hkc (1 : ZMod 3), mul_zero, add_zero]
  have hvk' : βL (Additive.ofMul s) kk = u' := by
    rw [hβLs_eq, Pi.add_apply, Pi.smul_apply, Pi.smul_apply]
    rw [qtwoDB16_dSign_one_apply m a b kk,
      Pi.single_eq_of_ne (M := fun _ => ZMod 3) hkc (1 : ZMod 3)]
    rw [if_neg (by tauto), smul_eq_mul, mul_one, smul_zero, add_zero]
  have h1 : u = -u' := by rw [← hva, hva']
  have h2 : u = u' := by rw [← hvk, hvk']
  have h1' : u = -u := by
    calc u = -u' := h1
      _ = -u := by rw [← h2]
  have h2u : (2 : ZMod 3) * u = 0 := by
    rw [two_mul]
    nth_rewrite 1 [h1']
    exact neg_add_cancel u
  have hu : u = 0 := by
    have h4 : (2 : ZMod 3) * 2 = 1 := by decide
    calc u = 1 * u := by rw [one_mul]
      _ = (2 * 2 : ZMod 3) * u := by rw [h4]
      _ = 2 * ((2 : ZMod 3) * u) := by rw [mul_assoc]
      _ = 0 := by rw [h2u, mul_zero]
  have hc0 : u + v = 0 := by
    have h := congrFun huv c
    rw [hs] at h
    simpa [Pi.add_apply, Pi.smul_apply, Pi.one_apply, Pi.single_eq_same, mul_one] using h
  have hv : v = 0 := by
    rw [hu, zero_add] at hc0
    exact hc0
  have huv0 : βL (Additive.ofMul s) = 0 := by
    rw [← huv, hu, hv]
    simp
  exact ofMul_eq_zero.mp (βL.injective (by rw [huv0, map_zero]))

end CFSG.StandardType.QTwo

end
