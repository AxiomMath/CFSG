module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Gorenstein.Chapter8_2

namespace CFSG
end CFSG
open CFSG

/-!
# Huppert--Blackburn X.1.12, Thompson--Bender

This file records the Lean-facing statement of the Thompson--Bender theorem
from Huppert--Blackburn, Vol. III, Chapter X, Theorem 1.12.

The expanded proof route lives in
`FeitThompson/TBS/full-proof/thompson_bender_signalizer_lemma.tex`, and the
Lean-oriented decomposition lives in
`FeitThompson/TBS/step-proof/thompson_bender_signalizer_lemma/`.
-/

open scoped Pointwise commutatorElement IsMulCommutative

universe u

/--
Book-faithful statement of Huppert--Blackburn X.1.12.

For odd prime `p`, if `A` is a `p`-subgroup of the `p`-constrained group `G`,
every order-`p` element of `C_G(A)` lies in `A`, `A` normalizes `K`, and
`K ∩ A = 1`, then `K ≤ O_{p'}(G)`.
-/
@[expose]
public def CFSG.thompsonBenderSignalizerLemmaStatement
    (G : Type u) [Group G] [Finite G]
    (p : ℕ) [Fact p.Prime] : Prop :=
  p ≠ 2 →
    PConstrainedGroup (G := G) p →
      ∀ A K : Subgroup G,
        IsPGroup p A →
          (∀ x : G,
            x ∈ Subgroup.centralizer (A : Set G) → orderOf x = p → x ∈ A) →
            A ≤ Subgroup.normalizer (K : Set G) →
              K ⊓ A = ⊥ →
                K ≤ pPrimeCore p G

/--
The immediate order-`p` obstruction used in X.1.10(c): under the
Thompson--Bender centralizer hypothesis, an element of `K` of order `p` that
centralizes `A` must be trivial.
-/
public theorem CFSG.thompson_bender_eq_one_of_mem_K_centralizer_order_p
    {G : Type u} [Group G]
    {p : ℕ} [Fact p.Prime]
    {A K : Subgroup G}
    (hcentral_order_p :
      ∀ x : G,
        x ∈ Subgroup.centralizer (A : Set G) → orderOf x = p → x ∈ A)
    (hK_inf_A : K ⊓ A = ⊥)
    {x : G} (hxK : x ∈ K)
    (hxcentral : x ∈ Subgroup.centralizer (A : Set G))
    (hxorder : orderOf x = p) :
    x = 1 := by
  have hxA : x ∈ A := hcentral_order_p x hxcentral hxorder
  have hxbot : x ∈ (⊥ : Subgroup G) := by
    simpa [hK_inf_A] using (show x ∈ K ⊓ A from ⟨hxK, hxA⟩)
  simpa using hxbot

/-- A normal subgroup of order prime to `p` is contained in `O_{p'}(G)`. -/
public theorem CFSG.thompson_bender_le_pPrimeCore_of_normal_coprime
    {G : Type u} [Group G]
    (p : ℕ) {K : Subgroup G} [K.Normal]
    (hK_coprime : Nat.Coprime p (Nat.card K)) :
    K ≤ pPrimeCore p G := by
  exact
    le_sSup
      (show K ∈ {L : Subgroup G | L.Normal ∧ Nat.Coprime p (Nat.card L)} from
        ⟨inferInstance, hK_coprime⟩)

/--
If a subgroup lies in `O_{p',p}(G)` and has order prime to `p`, then it lies in
`O_{p'}(G)`.
-/
public theorem CFSG.thompson_bender_le_pPrimeCore_of_le_Op_p'p
    {G : Type u} [Group G]
    {p : ℕ} [Fact p.Prime]
    {K : Subgroup G}
    (hK_le : K ≤ Op_p'p p G)
    (hK_coprime : Nat.Coprime p (Nat.card K)) :
    K ≤ pPrimeCore p G :=
  le_pPrimeCore_of_le_Op_p'p_of_coprime (G := G) (p := p) hK_le hK_coprime

/--
In the quotient by `O_{p'}(G)`, the `p`-constrained hypothesis says that
`O_p` controls its own centralizer.
-/
public theorem CFSG.thompson_bender_centralizer_pCore_quotient_le_pCore
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime]
    (hconstrained : PConstrainedGroup (G := G) p) :
    Subgroup.centralizer
        (pCore p (G ⧸ pPrimeCore p G) : Set (G ⧸ pPrimeCore p G)) ≤
      pCore p (G ⧸ pPrimeCore p G) := by
  classical
  let M : Subgroup G := pPrimeCore p G
  let q : G →* G ⧸ M := QuotientGroup.mk' M
  let T : Sylow p (Op_p'p p G) := Classical.choice (Sylow.nonempty (p := p) (G := Op_p'p p G))
  let TG : Subgroup G := T.1.map (Op_p'p p G).subtype
  let Tbar : Subgroup (G ⧸ M) := TG.map q
  have hqsurj : Function.Surjective q := QuotientGroup.mk'_surjective M
  have hMnormal : M.Normal := by
    dsimp [M]
    infer_instance
  let : M.Normal := hMnormal
  have hMcop : Nat.Coprime p (Nat.card M) := by
    simpa [M] using (pPrimeCore_coprime_card (G := G) (p := p))
  have hTG_p : IsPGroup p TG := by
    simpa [TG] using
      (IsPGroup.map (p := p) (H := (T : Subgroup (Op_p'p p G))) T.isPGroup'
        (Op_p'p p G).subtype)
  have hTG_le_op : TG ≤ Op_p'p p G := by
    simpa [TG] using
      (Subgroup.map_subtype_le (H := Op_p'p p G) (K := (T : Subgroup (Op_p'p p G))))
  have hmap_op : (Op_p'p p G).map q = pCore p (G ⧸ M) := by
    dsimp [Op_p'p, q, M]
    simpa using
      (Subgroup.map_comap_eq_self_of_surjective
        (f := QuotientGroup.mk' (pPrimeCore p G))
        (h := QuotientGroup.mk'_surjective (pPrimeCore p G))
        (H := pCore p (G ⧸ pPrimeCore p G)))
  have hTbar_le_pcore : Tbar ≤ pCore p (G ⧸ M) := by
    exact (Subgroup.map_mono hTG_le_op).trans hmap_op.le
  let f : Op_p'p p G →* pCore p (G ⧸ M) :=
    ((q.comp (Op_p'p p G).subtype)).codRestrict (pCore p (G ⧸ M)) (by
      intro x
      have hxmap : (q (x : G) : G ⧸ M) ∈ (Op_p'p p G).map q :=
        Subgroup.mem_map.mpr ⟨(x : G), x.property, rfl⟩
      exact hmap_op ▸ hxmap)
  have hf_surj : Function.Surjective f := by
    intro y
    rcases hqsurj y.1 with ⟨x, hx⟩
    refine ⟨⟨x, ?_⟩, ?_⟩
    · have hxmem : (q x : G ⧸ M) ∈ pCore p (G ⧸ M) := by simp [hx]
      simpa [Op_p'p, q, M] using hxmem
    · apply Subtype.ext
      simpa [f] using hx
  have hmapf_eq :
      (Subgroup.map f (T : Subgroup (Op_p'p p G))).map (pCore p (G ⧸ M)).subtype = Tbar := by
    ext z
    constructor
    · intro hz
      rcases Subgroup.mem_map.mp hz with ⟨x, hx, hxz⟩
      rcases Subgroup.mem_map.mp hx with ⟨t, ht, htx⟩
      refine Subgroup.mem_map.mpr ?_
      refine ⟨(t : Op_p'p p G), ?_, ?_⟩
      · exact Subgroup.mem_map.mpr ⟨t, ht, rfl⟩
      · rw [← hxz]
        exact congrArg Subtype.val htx
    · intro hz
      rcases Subgroup.mem_map.mp hz with ⟨x, hx, hxz⟩
      rcases Subgroup.mem_map.mp hx with ⟨t, ht, htx⟩
      refine Subgroup.mem_map.mpr ?_
      refine ⟨f t, ?_, ?_⟩
      · exact Subgroup.mem_map.mpr ⟨t, ht, rfl⟩
      · rw [← hxz]
        simpa [f] using congrArg q htx
  have hT_not_dvd : ¬ p ∣ (T : Subgroup (Op_p'p p G)).index := T.not_dvd_index
  have hidx_dvd :
      (Subgroup.map f (T : Subgroup (Op_p'p p G))).index ∣
        (T : Subgroup (Op_p'p p G)).index :=
    Subgroup.index_map_dvd (H := (T : Subgroup (Op_p'p p G))) (f := f) hf_surj
  have hmapf_not_dvd : ¬ p ∣ (Subgroup.map f (T : Subgroup (Op_p'p p G))).index := by
    intro hp_dvd
    exact hT_not_dvd (hp_dvd.trans hidx_dvd)
  have hpcore_p : IsPGroup p (pCore p (G ⧸ M)) :=
    pCore_isPGroup (p := p) (G := G ⧸ M)
  have hpow_idx :
      ∃ n, (Subgroup.map f (T : Subgroup (Op_p'p p G))).index = p ^ n := by
    exact IsPGroup.index (hG := hpcore_p) (H := Subgroup.map f (T : Subgroup (Op_p'p p G)))
  rcases hpow_idx with ⟨n, hn⟩
  have hnzero : n = 0 := by
    cases n with
    | zero => rfl
    | succ n =>
        exfalso
        apply hmapf_not_dvd
        refine ⟨p ^ n, ?_⟩
        rw [hn]
        simp [Nat.pow_succ, Nat.mul_comm]
  have hidx_one : (Subgroup.map f (T : Subgroup (Op_p'p p G))).index = 1 := by
    rw [hn, hnzero]
    simp
  have hmapf_top : Subgroup.map f (T : Subgroup (Op_p'p p G)) = ⊤ :=
    (Subgroup.index_eq_one).1 hidx_one
  have hTbar_eq_pcore : Tbar = pCore p (G ⧸ M) := by
    have htop_map :
        (⊤ : Subgroup (pCore p (G ⧸ M))).map (pCore p (G ⧸ M)).subtype =
          pCore p (G ⧸ M) := by
      let K : Subgroup (G ⧸ M) := pCore p (G ⧸ M)
      have hsubtop : K.subgroupOf K = ⊤ := (Subgroup.subgroupOf_eq_top).2 le_rfl
      calc
        (⊤ : Subgroup K).map K.subtype = (K.subgroupOf K).map K.subtype := by rw [hsubtop]
        _ = K ⊓ K := Subgroup.subgroupOf_map_subtype (H := K) (K := K)
        _ = K := inf_eq_right.mpr le_rfl
    have hEq :
        Tbar = (⊤ : Subgroup (pCore p (G ⧸ M))).map (pCore p (G ⧸ M)).subtype := by
      calc
        Tbar = (Subgroup.map f (T : Subgroup (Op_p'p p G))).map (pCore p (G ⧸ M)).subtype := by
          exact hmapf_eq.symm
        _ = (⊤ : Subgroup (pCore p (G ⧸ M))).map (pCore p (G ⧸ M)).subtype := by
          rw [hmapf_top]
    exact hEq.trans htop_map
  have hM_le_comap_opmap : M ≤ Subgroup.comap q ((Op_p'p p G).map q) := by
    intro x hx
    change q x ∈ (Op_p'p p G).map q
    have hx1 : q x = 1 := by
      simpa [q, M] using hx
    rw [hx1]
    simp
  have hTG_sup : M ⊔ TG = Op_p'p p G := by
    calc
      M ⊔ TG = Subgroup.comap q (TG.map q) := by
        simp [q]
      _ = Subgroup.comap q Tbar := rfl
      _ = Subgroup.comap q (pCore p (G ⧸ M)) := by rw [hTbar_eq_pcore]
      _ = Subgroup.comap q ((Op_p'p p G).map q) := by rw [hmap_op]
      _ = Op_p'p p G := by
        rw [QuotientGroup.comap_map_mk' M (Op_p'p p G)]
        exact sup_eq_right.mpr <| by
          dsimp [M, Op_p'p]
          exact QuotientGroup.le_comap_mk' (pPrimeCore p G) (pCore p (G ⧸ pPrimeCore p G))
  have hcent_TG : Subgroup.centralizer (TG : Set G) ≤ Op_p'p p G :=
    hconstrained (Q := TG) hTG_p hTG_sup
  have hcent_Tbar :
      Subgroup.centralizer (Tbar : Set (G ⧸ M)) ≤ pCore p (G ⧸ M) := by
    let : Fact (IsPGroup p (↥TG)) := ⟨hTG_p⟩
    have hcent_map :
        Subgroup.centralizer ((TG.map q : Subgroup (G ⧸ M)) : Set (G ⧸ M)) =
          (Subgroup.centralizer (TG : Set G)).map q := by
      simpa [q] using
        (centralizer_map_quotient_eq_map_centralizer (G := G) (p := p)
          (T := TG) (M := M) hMnormal hMcop)
    have hcent_map' :
        Subgroup.centralizer (Tbar : Set (G ⧸ M)) =
          (Subgroup.centralizer (TG : Set G)).map q := by
      simpa [Tbar] using hcent_map
    rw [hcent_map']
    exact (Subgroup.map_mono hcent_TG).trans hmap_op.le
  have hcore_bot : pPrimeCore p (G ⧸ M) = ⊥ := by
    simpa [M] using pPrimeCore_quotient_pPrimeCore_eq_bot (G := G) (p := p)
  have hOp_eq : Op_p'p p (G ⧸ M) = pCore p (G ⧸ M) := by
    exact Op_p'p_eq_pCore_of_pPrimeCore_eq_bot (G := G ⧸ M) (p := p) hcore_bot
  have hcent_pcore :
      Subgroup.centralizer (pCore p (G ⧸ M) : Set (G ⧸ M)) ≤ pCore p (G ⧸ M) := by
    simpa [hTbar_eq_pcore] using hcent_Tbar
  simpa [M] using hcent_pcore

/--
Endpoint for the reduced route: if the image of `K` in `G/O_{p'}(G)`
centralizes `O_p`, then p-constrainedness puts `K` in `O_{p',p}(G)`.
-/
public theorem CFSG.thompson_bender_le_Op_p'p_of_map_le_centralizer_pCore_quotient
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime]
    (hconstrained : PConstrainedGroup (G := G) p)
    {K : Subgroup G}
    (hK_map_cent :
      let q : G →* G ⧸ pPrimeCore p G := QuotientGroup.mk' (pPrimeCore p G)
      K.map q ≤
        Subgroup.centralizer
          (pCore p (G ⧸ pPrimeCore p G) : Set (G ⧸ pPrimeCore p G))) :
    K ≤ Op_p'p p G := by
  classical
  let q : G →* G ⧸ pPrimeCore p G := QuotientGroup.mk' (pPrimeCore p G)
  intro x hxK
  have hxmap : q x ∈ K.map q := Subgroup.mem_map_of_mem q hxK
  have hxcent :
      q x ∈
        Subgroup.centralizer
          (pCore p (G ⧸ pPrimeCore p G) : Set (G ⧸ pPrimeCore p G)) :=
    hK_map_cent hxmap
  have hxpcore : q x ∈ pCore p (G ⧸ pPrimeCore p G) :=
    thompson_bender_centralizer_pCore_quotient_le_pCore
      (G := G) (p := p) hconstrained hxcent
  simpa [Op_p'p, q] using hxpcore

/--
Huppert--Blackburn X.1.10(c), isolated in the form needed by X.1.12:
the signalizer subgroup has order prime to `p`.
-/
public theorem CFSG.thompson_bender_coprime_card_of_centralizer_order_p
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime]
    {A K : Subgroup G}
    (hA_p : IsPGroup p A)
    (hcentral_order_p :
      ∀ x : G,
        x ∈ Subgroup.centralizer (A : Set G) → orderOf x = p → x ∈ A)
    (hA_le_normalizer_K : A ≤ Subgroup.normalizer (K : Set G))
    (hK_inf_A : K ⊓ A = ⊥) :
    Nat.Coprime p (Nat.card K) := by
  classical
  refine (Nat.Prime.coprime_iff_not_dvd (Fact.out : Nat.Prime p)).2 ?_
  intro hp_dvd_K
  let : Subgroup.Normalizes A K := ⟨hA_le_normalizer_K⟩
  have hfixed_dvd :
      p ∣ Nat.card (fixedPointSubgroup (↥A) (↥K)) := by
    have hmod :
        Nat.card (↥K) ≡ Nat.card (MulAction.fixedPoints (↥A) (↥K)) [MOD p] :=
      hA_p.card_modEq_card_fixedPoints (↥K)
    have hfixed_set_dvd : p ∣ Nat.card (MulAction.fixedPoints (↥A) (↥K)) :=
      Nat.modEq_zero_iff_dvd.mp (hmod.symm.trans hp_dvd_K.modEq_zero_nat)
    change p ∣ Nat.card (MulAction.fixedPoints (↥A) (↥K))
    exact hfixed_set_dvd
  obtain ⟨x, hx_order⟩ :=
    exists_prime_orderOf_dvd_card' (G := fixedPointSubgroup (↥A) (↥K)) p hfixed_dvd
  have hxK : (((x : fixedPointSubgroup (↥A) (↥K)) : K) : G) ∈ K :=
    ((x : fixedPointSubgroup (↥A) (↥K)) : K).property
  have hxcentral : (((x : fixedPointSubgroup (↥A) (↥K)) : K) : G) ∈
      Subgroup.centralizer (A : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro a haA
    let aA : A := ⟨a, haA⟩
    have hfix :
        aA • ((x : fixedPointSubgroup (↥A) (↥K)) : K) =
          ((x : fixedPointSubgroup (↥A) (↥K)) : K) := by
      exact
        (FixedPoints.mem_subgroup (M := (↥A)) (α := (↥K))
          ((x : fixedPointSubgroup (↥A) (↥K)) : K)).1 x.property aA
    have hconj :
        a * (((x : fixedPointSubgroup (↥A) (↥K)) : K) : G) * a⁻¹ =
          (((x : fixedPointSubgroup (↥A) (↥K)) : K) : G) := by
      simpa [aA, Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe] using
        congrArg Subtype.val hfix
    simpa [mul_assoc] using congrArg (fun t : G => t * a) hconj
  have hx_order_G : orderOf (((x : fixedPointSubgroup (↥A) (↥K)) : K) : G) = p := by
    calc
      orderOf (((x : fixedPointSubgroup (↥A) (↥K)) : K) : G) =
          orderOf ((x : fixedPointSubgroup (↥A) (↥K)) : K) :=
        Subgroup.orderOf_coe _
      _ = orderOf x := Subgroup.orderOf_coe _
      _ = p := hx_order
  have hx_one : (((x : fixedPointSubgroup (↥A) (↥K)) : K) : G) = 1 :=
    thompson_bender_eq_one_of_mem_K_centralizer_order_p
      (G := G) (p := p) (A := A) (K := K)
      hcentral_order_p hK_inf_A hxK hxcentral hx_order_G
  have hp_eq_one : p = 1 := by
    calc
      p = orderOf (((x : fixedPointSubgroup (↥A) (↥K)) : K) : G) := hx_order_G.symm
      _ = 1 := by simp [hx_one]
  exact (Fact.out : Nat.Prime p).ne_one hp_eq_one

/--
The order-`p` centralizer hypothesis descends through the quotient by
`O_{p'}(G)`.
-/
public theorem CFSG.thompson_bender_quotient_centralizer_order_p
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime]
    {A : Subgroup G}
    (hA_p : IsPGroup p A)
    (hcentral_order_p :
      ∀ x : G,
        x ∈ Subgroup.centralizer (A : Set G) → orderOf x = p → x ∈ A)
    {x : G ⧸ pPrimeCore p G}
    (hxcentral :
      x ∈
        Subgroup.centralizer
          ((A.map (QuotientGroup.mk' (pPrimeCore p G)) :
            Subgroup (G ⧸ pPrimeCore p G)) : Set (G ⧸ pPrimeCore p G)))
    (hxorder : orderOf x = p) :
    x ∈ A.map (QuotientGroup.mk' (pPrimeCore p G)) := by
  classical
  let M : Subgroup G := pPrimeCore p G
  let q : G →* G ⧸ M := QuotientGroup.mk' M
  let C : Subgroup G := Subgroup.centralizer (A : Set G)
  let Z : Subgroup (G ⧸ M) := Subgroup.zpowers x
  let U : Subgroup G := C ⊓ Subgroup.comap q Z
  have hMnormal : M.Normal := by
    dsimp [M]
    infer_instance
  let : M.Normal := hMnormal
  have hMcop : Nat.Coprime p (Nat.card M) := by
    simpa [M] using (pPrimeCore_coprime_card (G := G) (p := p))
  let : Fact (IsPGroup p (↥A)) := ⟨hA_p⟩
  have hcent_eq :
      Subgroup.centralizer ((A.map q : Subgroup (G ⧸ M)) : Set (G ⧸ M)) =
        C.map q := by
    simpa [C, q, M] using
      (centralizer_map_quotient_eq_map_centralizer (G := G) (p := p)
        (T := A) (M := M) hMnormal hMcop)
  have hxcentral_q :
      x ∈ Subgroup.centralizer ((A.map q : Subgroup (G ⧸ M)) : Set (G ⧸ M)) := by
    simpa [q, M] using hxcentral
  have hxCmap : x ∈ C.map q := by
    rwa [hcent_eq] at hxcentral_q
  rcases Subgroup.mem_map.mp hxCmap with ⟨c, hcC, hcx⟩
  have hZ_le_Umap : Z ≤ U.map q := by
    intro z hz
    rcases Subgroup.mem_zpowers_iff.mp hz with ⟨n, hn⟩
    refine Subgroup.mem_map.mpr ?_
    refine ⟨c ^ n, ?_, ?_⟩
    · constructor
      · exact C.zpow_mem hcC n
      · change q (c ^ n) ∈ Z
        rw [map_zpow, hcx]
        exact Z.zpow_mem (Subgroup.mem_zpowers x) n
    · rw [map_zpow, hcx, hn]
  have hZcard : Nat.card Z = p := by
    dsimp [Z]
    rw [Nat.card_zpowers, hxorder]
  have hp_dvd_U : p ∣ Nat.card U := by
    have hp_dvd_Umap : p ∣ Nat.card (U.map q) := by
      rw [← hZcard]
      exact Subgroup.card_dvd_of_le hZ_le_Umap
    exact hp_dvd_Umap.trans (Subgroup.card_map_dvd U q)
  obtain ⟨yU, hy_order_U⟩ :=
    exists_prime_orderOf_dvd_card' (G := U) p hp_dvd_U
  let y : G := yU
  have hyC : y ∈ C := yU.property.1
  have hyZ : q y ∈ Z := yU.property.2
  have hyorder : orderOf y = p := by
    simpa [y, Subgroup.orderOf_coe] using hy_order_U
  have hyA : y ∈ A := hcentral_order_p y hyC hyorder
  have hyqA : q y ∈ A.map q := Subgroup.mem_map_of_mem q hyA
  have hyq_ne_one : q y ≠ 1 := by
    intro hyq_one
    have hyM : y ∈ M := (QuotientGroup.eq_one_iff (N := M) y).1 hyq_one
    have hyM_order : orderOf (⟨y, hyM⟩ : M) = p := by
      simpa [Subgroup.orderOf_coe] using hyorder
    have hp_dvd_M : p ∣ Nat.card M := by
      rw [← hyM_order]
      exact orderOf_dvd_natCard (⟨y, hyM⟩ : M)
    exact ((Nat.Prime.coprime_iff_not_dvd (Fact.out : Nat.Prime p)).1 hMcop) hp_dvd_M
  let Y : Subgroup (G ⧸ M) := Subgroup.zpowers (q y)
  have hY_le_Z : Y ≤ Z := (Subgroup.zpowers_le).2 hyZ
  have hYcard_dvd_p : Nat.card Y ∣ p := by
    rw [← hZcard]
    exact Subgroup.card_dvd_of_le hY_le_Z
  have hYcard_ne_one : Nat.card Y ≠ 1 := by
    intro hYcard
    have hYbot : Y = ⊥ := (Subgroup.card_eq_one).1 hYcard
    have hyq_bot : q y ∈ (⊥ : Subgroup (G ⧸ M)) := by
      simpa [Y, hYbot] using (Subgroup.mem_zpowers (q y))
    exact hyq_ne_one (by simpa using hyq_bot)
  have hYcard_eq_p : Nat.card Y = p :=
    ((Fact.out : Nat.Prime p).eq_one_or_self_of_dvd (Nat.card Y) hYcard_dvd_p).resolve_left
      hYcard_ne_one
  have hY_eq_Z : Y = Z := by
    apply Subgroup.eq_of_le_of_card_ge hY_le_Z
    rw [hYcard_eq_p, hZcard]
  have hxY : x ∈ Y := by
    rw [hY_eq_Z]
    exact Subgroup.mem_zpowers x
  have hY_le_Amap : Y ≤ A.map q := (Subgroup.zpowers_le).2 hyqA
  exact hY_le_Amap hxY

/-- The image of a `p'` signalizer subgroup in the quotient by `O_{p'}` is still `p'`. -/
public theorem CFSG.thompson_bender_quotient_signalizer_coprime_card
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime]
    {K : Subgroup G}
    (hK_coprime : Nat.Coprime p (Nat.card K)) :
    Nat.Coprime p
      (Nat.card (K.map (QuotientGroup.mk' (pPrimeCore p G)))) := by
  classical
  let q : G →* G ⧸ pPrimeCore p G := QuotientGroup.mk' (pPrimeCore p G)
  refine (Nat.Prime.coprime_iff_not_dvd (Fact.out : Nat.Prime p)).2 ?_
  intro hp_dvd
  exact
    ((Nat.Prime.coprime_iff_not_dvd (Fact.out : Nat.Prime p)).1 hK_coprime)
      (hp_dvd.trans (Subgroup.card_map_dvd K q))

/-- The image of the `p`-subgroup `A` in the quotient by `O_{p'}` is a `p`-subgroup. -/
public theorem CFSG.thompson_bender_quotient_A_isPGroup
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime]
    {A : Subgroup G}
    (hA_p : IsPGroup p A) :
    IsPGroup p (A.map (QuotientGroup.mk' (pPrimeCore p G))) := by
  classical
  exact IsPGroup.map (p := p) (H := A) hA_p (QuotientGroup.mk' (pPrimeCore p G))

/-- Normalizer membership of `A` over `K` descends to their quotient images. -/
public theorem CFSG.thompson_bender_quotient_A_le_normalizer_K
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime]
    {A K : Subgroup G}
    (hA_le_normalizer_K : A ≤ Subgroup.normalizer (K : Set G)) :
    let q : G →* G ⧸ pPrimeCore p G := QuotientGroup.mk' (pPrimeCore p G)
    A.map q ≤ Subgroup.normalizer (K.map q : Set (G ⧸ pPrimeCore p G)) := by
  classical
  intro q y hy
  rcases Subgroup.mem_map.mp hy with ⟨a, haA, rfl⟩
  rw [Subgroup.mem_normalizer_iff]
  intro z
  constructor
  · intro hz
    rcases Subgroup.mem_map.mp hz with ⟨k, hkK, hkz⟩
    refine Subgroup.mem_map.mpr ?_
    refine ⟨a * k * a⁻¹, ?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.mp (hA_le_normalizer_K haA) k).1 hkK
    · rw [map_mul, map_mul, MonoidHom.map_inv, hkz]
  · intro hz
    rcases Subgroup.mem_map.mp hz with ⟨k, hkK, hkz⟩
    refine Subgroup.mem_map.mpr ?_
    refine ⟨a⁻¹ * k * a, ?_, ?_⟩
    · simpa using
        (Subgroup.mem_normalizer_iff.mp
          (Subgroup.inv_mem (Subgroup.normalizer (K : Set G)) (hA_le_normalizer_K haA)) k).1 hkK
    · rw [map_mul, map_mul, MonoidHom.map_inv, hkz]
      simp [mul_assoc]

/-- In the quotient by `O_{p'}`, the images of `K` and `A` still intersect trivially. -/
public theorem CFSG.thompson_bender_quotient_K_inf_A_eq_bot
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime]
    {A K : Subgroup G}
    (hA_p : IsPGroup p A)
    (hK_coprime : Nat.Coprime p (Nat.card K)) :
    let q : G →* G ⧸ pPrimeCore p G := QuotientGroup.mk' (pPrimeCore p G)
    K.map q ⊓ A.map q = ⊥ := by
  classical
  intro q
  have hKq_coprime :
      Nat.Coprime p (Nat.card (K.map q)) := by
    simpa [q] using
      (thompson_bender_quotient_signalizer_coprime_card
        (G := G) (p := p) (K := K) hK_coprime)
  have hAq_p : IsPGroup p (A.map q) := by
    simpa [q] using
      (thompson_bender_quotient_A_isPGroup (G := G) (p := p) (A := A) hA_p)
  rcases hAq_p.exists_card_eq with ⟨n, hAq_card⟩
  have hp_not_dvd_Kq : ¬ p ∣ Nat.card (K.map q) :=
    (Nat.Prime.coprime_iff_not_dvd (Fact.out : Nat.Prime p)).1 hKq_coprime
  have hcop :
      Nat.Coprime (Nat.card (K.map q)) (Nat.card (A.map q)) := by
    rw [hAq_card]
    exact (Fact.out : Nat.Prime p).coprime_pow_of_not_dvd (m := n) hp_not_dvd_Kq
  exact disjoint_iff.mp (Subgroup.disjoint_of_coprime_natCard hcop)

/--
If an element lies in both `A` and `O_p(G)`, then it centralizes the `p'`
signalizer subgroup normalized by `A`.
-/
public theorem CFSG.thompson_bender_mem_A_inf_pCore_centralizes_K
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime]
    {A K : Subgroup G}
    (hA_le_normalizer_K : A ≤ Subgroup.normalizer (K : Set G))
    (hK_coprime : Nat.Coprime p (Nat.card K))
    {x : G} (hxA : x ∈ A) (hxP : x ∈ pCore p G) :
    x ∈ Subgroup.centralizer (K : Set G) := by
  classical
  obtain ⟨n, hPcard⟩ := (pCore_isPGroup (G := G) (p := p)).exists_card_eq
  have hcopKP : Nat.Coprime (Nat.card K) (Nat.card (pCore p G)) := by
    rw [hPcard]
    exact hK_coprime.symm.pow_right n
  have hInf : K ⊓ pCore p G = ⊥ :=
    disjoint_iff.mp (Subgroup.disjoint_of_coprime_natCard hcopKP)
  rw [Subgroup.mem_centralizer_iff]
  intro k hk
  have hx_norm : x ∈ Subgroup.normalizer (K : Set G) := hA_le_normalizer_K hxA
  have hxkx_memK : x * k * x⁻¹ ∈ K :=
    (Subgroup.mem_normalizer_iff.mp hx_norm k).1 hk
  have hcommK : ⁅x, k⁆ ∈ K := by
    have hkinv : k⁻¹ ∈ K := K.inv_mem hk
    simpa [commutatorElement_def, mul_assoc] using K.mul_mem hxkx_memK hkinv
  have hcommP : ⁅x, k⁆ ∈ pCore p G := by
    have hxinvP : x⁻¹ ∈ pCore p G := (pCore p G).inv_mem hxP
    have hkxinvkP : k * x⁻¹ * k⁻¹ ∈ pCore p G :=
      Subgroup.Normal.conj_mem (inferInstance : (pCore p G).Normal) x⁻¹ hxinvP k
    simpa [commutatorElement_def, mul_assoc] using
      (pCore p G).mul_mem hxP hkxinvkP
  have hcommInf : ⁅x, k⁆ ∈ K ⊓ pCore p G := ⟨hcommK, hcommP⟩
  have hcommBot : ⁅x, k⁆ ∈ (⊥ : Subgroup G) := by
    simpa [hInf] using hcommInf
  have hcommOne : ⁅x, k⁆ = 1 := by
    simpa using hcommBot
  exact (commutatorElement_eq_one_iff_mul_comm.mp hcommOne).symm

/--
An order-`p` element of `O_p(G)` centralizing `A` centralizes `K`, because the
Thompson--Bender centralizer hypothesis puts it in `A`.
-/
public theorem CFSG.thompson_bender_order_p_pCore_mem_centralizer_A_centralizes_K
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime]
    {A K : Subgroup G}
    (hcentral_order_p :
      ∀ x : G,
        x ∈ Subgroup.centralizer (A : Set G) → orderOf x = p → x ∈ A)
    (hA_le_normalizer_K : A ≤ Subgroup.normalizer (K : Set G))
    (hK_coprime : Nat.Coprime p (Nat.card K))
    {x : G} (hxP : x ∈ pCore p G)
    (hxcentral : x ∈ Subgroup.centralizer (A : Set G))
    (hxorder : orderOf x = p) :
    x ∈ Subgroup.centralizer (K : Set G) := by
  exact
    thompson_bender_mem_A_inf_pCore_centralizes_K
      (G := G) (p := p) (A := A) (K := K)
      hA_le_normalizer_K hK_coprime
      (hcentral_order_p x hxcentral hxorder) hxP

/--
To prove that the conjugation image of `K` fixes a subgroup `D ≤ P`, it is
enough to show each element of `D` centralizes `K` in the ambient group.
-/
public theorem CFSG.thompson_bender_action_range_le_fixing_of_subtype_le_centralizer
    {G : Type u} [Group G]
    {P K : Subgroup G} [P.Normal] {D : Subgroup P}
    (hDcentK : ∀ x : P, x ∈ D → (x : G) ∈ Subgroup.centralizer (K : Set G)) :
    let hKleNormP : K ≤ Subgroup.normalizer (P : Set G) :=
      Subgroup.le_normalizer_of_normal (H := P)
    let φ : K →* MulAut P :=
      (Subgroup.normalizerMonoidHom (H := P)).comp (Subgroup.inclusion hKleNormP)
    φ.range ≤ fixingSubgroup (M := MulAut P) (α := P) (D : Set P) := by
  classical
  let hKleNormP : K ≤ Subgroup.normalizer (P : Set G) :=
    Subgroup.le_normalizer_of_normal (H := P)
  let φ : K →* MulAut P :=
    (Subgroup.normalizerMonoidHom (H := P)).comp (Subgroup.inclusion hKleNormP)
  change φ.range ≤ fixingSubgroup (M := MulAut P) (α := P) (D : Set P)
  intro ψ hψ
  rcases hψ with ⟨k, rfl⟩
  rw [mem_fixingSubgroup_iff]
  intro x hxD
  have hcomm : (k : G) * (x : G) = (x : G) * (k : G) := by
    simpa using
      (Subgroup.mem_centralizer_iff.mp (hDcentK x hxD) (k : G) k.property)
  have hconj : (k : G) * (x : G) * (k : G)⁻¹ = (x : G) := by
    simpa [mul_assoc] using congrArg (fun t : G => t * (k : G)⁻¹) hcomm
  apply Subtype.ext
  simpa [φ, hKleNormP, Subgroup.normalizerMonoidHom_apply_apply_coe] using hconj

/--
If the conjugation image of `K` fixes `D ≤ P`, then every element of `D`
centralizes `K` in the ambient group.
-/
public theorem CFSG.thompson_bender_subtype_le_centralizer_of_action_range_le_fixing
    {G : Type u} [Group G]
    {P K : Subgroup G} [P.Normal] {D : Subgroup P}
    (hRangeFix :
      let hKleNormP : K ≤ Subgroup.normalizer (P : Set G) :=
        Subgroup.le_normalizer_of_normal (H := P)
      let φ : K →* MulAut P :=
        (Subgroup.normalizerMonoidHom (H := P)).comp (Subgroup.inclusion hKleNormP)
      φ.range ≤ fixingSubgroup (M := MulAut P) (α := P) (D : Set P)) :
    ∀ x : P, x ∈ D → (x : G) ∈ Subgroup.centralizer (K : Set G) := by
  classical
  let hKleNormP : K ≤ Subgroup.normalizer (P : Set G) :=
    Subgroup.le_normalizer_of_normal (H := P)
  let φ : K →* MulAut P :=
    (Subgroup.normalizerMonoidHom (H := P)).comp (Subgroup.inclusion hKleNormP)
  change φ.range ≤ fixingSubgroup (M := MulAut P) (α := P) (D : Set P) at hRangeFix
  intro x hxD
  rw [Subgroup.mem_centralizer_iff]
  intro k hk
  let kK : K := ⟨k, hk⟩
  have hfix_mem : φ kK ∈ fixingSubgroup (M := MulAut P) (α := P) (D : Set P) :=
    hRangeFix ⟨kK, rfl⟩
  rw [mem_fixingSubgroup_iff] at hfix_mem
  have hfix_x : φ kK x = x := hfix_mem x hxD
  have hconj : k * (x : G) * k⁻¹ = (x : G) := by
    simpa [φ, kK, hKleNormP, Subgroup.normalizerMonoidHom_apply_apply_coe] using
      congrArg Subtype.val hfix_x
  simpa [mul_assoc] using congrArg (fun t : G => t * k) hconj

/--
If `D` is characteristic in `H`, then every element normalizing `H` also
normalizes the image of `D` in the ambient group.
-/
public theorem CFSG.thompson_bender_normalizer_le_normalizer_map_subtype_of_characteristic
    {G : Type u} [Group G]
    (H : Subgroup G) (D : Subgroup H) (hDchar : D.Characteristic) :
    Subgroup.normalizer (H : Set G) ≤
      Subgroup.normalizer ((D.map H.subtype : Subgroup G) : Set G) := by
  classical
  let : D.Characteristic := hDchar
  have hconj_mem :
      ∀ {g : G}, g ∈ Subgroup.normalizer (H : Set G) →
        ∀ {x : G}, x ∈ D.map H.subtype → g * x * g⁻¹ ∈ D.map H.subtype := by
    intro g hg x hx
    rcases Subgroup.mem_map.mp hx with ⟨xH, hxD, rfl⟩
    let gH : Subgroup.normalizer (H : Set G) := ⟨g, hg⟩
    have hfix :
        D.comap (Subgroup.normalizerMonoidHom H gH).toMonoidHom = D :=
      hDchar.fixed (Subgroup.normalizerMonoidHom H gH)
    have hxComap :
        xH ∈ D.comap (Subgroup.normalizerMonoidHom H gH).toMonoidHom := by
      rw [hfix]
      exact hxD
    exact ⟨(Subgroup.normalizerMonoidHom H gH) xH, hxComap, by
      simp [gH, mul_assoc, Subgroup.normalizerMonoidHom_apply_apply_coe]⟩
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact hconj_mem hg
  · intro hx
    have hginv : g⁻¹ ∈ Subgroup.normalizer (H : Set G) :=
      (Subgroup.normalizer (H : Set G)).inv_mem hg
    have hx' := hconj_mem hginv hx
    simpa [mul_assoc] using hx'

/-- A characteristic subgroup of `O_p(G)`, viewed in `G`, is normal. -/
public theorem CFSG.thompson_bender_pCore_characteristic_subgroup_map_normal
    {G : Type u} [Group G] {p : ℕ} {D : Subgroup (pCore p G)}
    (hDchar : D.Characteristic) :
    (D.map (pCore p G).subtype : Subgroup G).Normal := by
  have htop_le :
      (⊤ : Subgroup G) ≤
        Subgroup.normalizer ((D.map (pCore p G).subtype : Subgroup G) : Set G) := by
    intro g hg
    have hnormP : g ∈ Subgroup.normalizer ((pCore p G : Subgroup G) : Set G) := by
      exact
        (show (⊤ : Subgroup G) ≤
            Subgroup.normalizer ((pCore p G : Subgroup G) : Set G) from
          Subgroup.le_normalizer_of_normal (H := pCore p G)) hg
    exact
      thompson_bender_normalizer_le_normalizer_map_subtype_of_characteristic
        (G := G) (H := pCore p G) (D := D) hDchar hnormP
  have hnorm_top :
      Subgroup.normalizer ((D.map (pCore p G).subtype : Subgroup G) : Set G) = ⊤ :=
    le_antisymm le_top htop_le
  exact Subgroup.normalizer_eq_top_iff.mp hnorm_top

/-- Any ambient subgroup normalizes a characteristic subgroup of `O_p(G)`. -/
public theorem CFSG.thompson_bender_le_normalizer_pCore_characteristic_subgroup
    {G : Type u} [Group G] {p : ℕ} {D : Subgroup (pCore p G)}
    (hDchar : D.Characteristic) (L : Subgroup G) :
    L ≤ Subgroup.normalizer ((D.map (pCore p G).subtype : Subgroup G) : Set G) := by
  let : (D.map (pCore p G).subtype : Subgroup G).Normal :=
    thompson_bender_pCore_characteristic_subgroup_map_normal
      (G := G) (p := p) (D := D) hDchar
  exact Subgroup.le_normalizer_of_normal (H := D.map (pCore p G).subtype)

/--
Ambient centralizer containment for a subgroup of `O_p(G)` is equivalent to
the corresponding pointwise statement on the subtype witness.
-/
public theorem CFSG.thompson_bender_pCore_subgroup_map_le_centralizer_iff
    {G : Type u} [Group G] {p : ℕ} {D : Subgroup (pCore p G)} {K : Subgroup G} :
    D.map (pCore p G).subtype ≤ Subgroup.centralizer (K : Set G) ↔
      ∀ x : pCore p G, x ∈ D → (x : G) ∈ Subgroup.centralizer (K : Set G) := by
  constructor
  · intro hle x hxD
    exact hle (Subgroup.mem_map_of_mem (pCore p G).subtype hxD)
  · intro hpoint y hy
    rcases Subgroup.mem_map.mp hy with ⟨x, hxD, rfl⟩
    exact hpoint x hxD

/--
If the ambient image of `D ≤ O_p(G)` is not contained in `C_G(K)`, then some
element of `D` fails to commute with some element of `K`.
-/
public theorem CFSG.thompson_bender_exists_pCore_mem_noncentralizing_of_not_map_le_centralizer
    {G : Type u} [Group G] {p : ℕ} {D : Subgroup (pCore p G)} {K : Subgroup G}
    (hnot : ¬ D.map (pCore p G).subtype ≤ Subgroup.centralizer (K : Set G)) :
    ∃ x : pCore p G, x ∈ D ∧ ∃ k : G, k ∈ K ∧ k * (x : G) ≠ (x : G) * k := by
  classical
  have hnotPoint :
      ¬ ∀ x : pCore p G, x ∈ D → (x : G) ∈ Subgroup.centralizer (K : Set G) := by
    intro hpoint
    exact hnot ((thompson_bender_pCore_subgroup_map_le_centralizer_iff
      (G := G) (p := p) (D := D) (K := K)).2 hpoint)
  by_contra hnone
  apply hnotPoint
  intro x hxD
  rw [Subgroup.mem_centralizer_iff]
  intro k hk
  by_contra hne
  exact hnone ⟨x, hxD, k, hk, hne⟩

/--
If a subgroup `D ≤ O_p(G)` has exponent `p` and lies in the centralizer of
`A`, then `D` centralizes the `p'` signalizer subgroup `K`.
-/
public theorem CFSG.thompson_bender_pCore_exponent_p_subgroup_centralizes_K_of_le_centralizer_A
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {A K : Subgroup G}
    (hcentral_order_p :
      ∀ x : G,
        x ∈ Subgroup.centralizer (A : Set G) → orderOf x = p → x ∈ A)
    (hA_le_normalizer_K : A ≤ Subgroup.normalizer (K : Set G))
    (hK_coprime : Nat.Coprime p (Nat.card K))
    {D : Subgroup (pCore p G)}
    (hDexp : Monoid.exponent (↥D) = p)
    (hDcentA : ∀ x : pCore p G, x ∈ D → (x : G) ∈ Subgroup.centralizer (A : Set G)) :
    ∀ x : pCore p G, x ∈ D → (x : G) ∈ Subgroup.centralizer (K : Set G) := by
  intro x hxD
  by_cases hxone : x = 1
  · subst hxone
    simp
  · let xD : D := ⟨x, hxD⟩
    have hxD_ne : xD ≠ 1 := by
      intro hxD_one
      exact hxone (by simpa [xD] using congrArg Subtype.val hxD_one)
    have hxpowD : xD ^ p = 1 := by
      have hdiv : Monoid.exponent (↥D) ∣ p := by simp [hDexp]
      exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hdiv xD
    have hxorderD : orderOf xD = p := orderOf_eq_prime hxpowD hxD_ne
    have hxorderP : orderOf x = p := by
      simpa [xD, Subgroup.orderOf_coe] using hxorderD
    have hxorderG : orderOf (x : G) = p := by
      simpa [Subgroup.orderOf_coe] using hxorderP
    exact
      thompson_bender_order_p_pCore_mem_centralizer_A_centralizes_K
        (G := G) (p := p) (A := A) (K := K)
        hcentral_order_p hA_le_normalizer_K hK_coprime
        x.property (hDcentA x hxD) hxorderG

/--
If the conjugation image of a `p'` subgroup `K` on a normal subgroup `P` lands
in a `p`-group of automorphisms fixing `D`, then `K` centralizes `P`.
-/
public theorem CFSG.thompson_bender_le_centralizer_of_coprime_action_range_le_fixing
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {P K : Subgroup G} [P.Normal] {D : Subgroup P}
    (hK_coprime : Nat.Coprime p (Nat.card K))
    (hfix : IsPGroup p
      (↥(fixingSubgroup (M := MulAut P) (α := P) (D : Set P))))
    (hRangeFix :
      let hKleNormP : K ≤ Subgroup.normalizer (P : Set G) :=
        Subgroup.le_normalizer_of_normal (H := P)
      let φ : K →* MulAut P :=
        (Subgroup.normalizerMonoidHom (H := P)).comp (Subgroup.inclusion hKleNormP)
      φ.range ≤ fixingSubgroup (M := MulAut P) (α := P) (D : Set P)) :
    K ≤ Subgroup.centralizer (P : Set G) := by
  classical
  let hKleNormP : K ≤ Subgroup.normalizer (P : Set G) :=
    Subgroup.le_normalizer_of_normal (H := P)
  let φ : K →* MulAut P :=
    (Subgroup.normalizerMonoidHom (H := P)).comp (Subgroup.inclusion hKleNormP)
  let F : Subgroup (MulAut P) := fixingSubgroup (M := MulAut P) (α := P) (D : Set P)
  let R : Subgroup (MulAut P) := φ.range
  have hRF : R ≤ F := by
    simpa [R, F, φ, hKleNormP] using hRangeFix
  have hRcop : Nat.Coprime p (Nat.card R) := by
    exact Nat.Coprime.of_dvd_right (Subgroup.card_range_dvd φ) hK_coprime
  let RF : Subgroup F := R.subgroupOf F
  have hRFp : IsPGroup p RF := hfix.to_subgroup RF
  have hRFcard : Nat.card RF = Nat.card R := by
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (H := R) (K := F) hRF).toEquiv
  obtain ⟨n, hRcard_p⟩ := hRFp.exists_card_eq
  have hRcard_p' : Nat.card R = p ^ n := by
    simpa [hRFcard] using hRcard_p
  have hRcard_one : Nat.card R = 1 := by
    have hcop_pow : Nat.Coprime p (p ^ n) := by
      simpa [hRcard_p'] using hRcop
    have hnzero : n = 0 := by
      by_contra hn0
      have hpdvd : p ∣ p ^ n := dvd_pow_self p (Nat.pos_iff_ne_zero.mpr hn0).ne'
      exact ((Fact.out : Nat.Prime p).coprime_iff_not_dvd.mp hcop_pow) hpdvd
    simp [hRcard_p', hnzero]
  have hRbot : R = ⊥ := (Subgroup.card_eq_one (H := R)).1 hRcard_one
  intro k hk
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  let kK : K := ⟨k, hk⟩
  let yP : P := ⟨y, hy⟩
  have hφ_mem : φ kK ∈ R := by
    exact ⟨kK, rfl⟩
  have hφ_one : φ kK = 1 := by
    have hφ_bot : φ kK ∈ (⊥ : Subgroup (MulAut P)) := by
      simpa [hRbot] using hφ_mem
    simpa using hφ_bot
  have hfix_y : φ kK yP = yP := by
    simp [hφ_one]
  have hconj : k * y * k⁻¹ = y := by
    simpa [φ, kK, yP, Subgroup.normalizerMonoidHom_apply_apply_coe] using
      congrArg Subtype.val hfix_y
  have hcomm : k * y = y * k := by
    simpa [mul_assoc] using congrArg (fun t : G => t * k) hconj
  exact hcomm.symm

/--
The source proof chooses a minimal subgroup from the family `Γ`.  This
predicate is the Lean-facing version of a witness for membership in that
family: `X ≤ O_p(G)` carries a critical witness `D` whose ambient image is
normalized by `A ⊔ K`, while `K` does not centralize that image.
-/
@[expose]
public def CFSG.TBSGammaWitness {G : Type u} [Group G] (p : ℕ) (A K : Subgroup G)
    (X D : Subgroup (pCore p G)) : Prop :=
  D ≤ X ∧
    D.Characteristic ∧
      (⁅D, ⊤⁆ ≤ centerIn (G := pCore p G) D) ∧
        NilpotencyClassLe 2 (↥D) ∧
          Monoid.exponent (↥D) = p ∧
            let Damb : Subgroup G := D.map (pCore p G).subtype
            A ⊔ K ≤ Subgroup.normalizer (Damb : Set G) ∧
              ¬ Damb ≤ Subgroup.centralizer (K : Set G)

/-- Membership in the source family `Γ`. -/
@[expose]
public def CFSG.TBSGamma {G : Type u} [Group G] (p : ℕ) (A K : Subgroup G)
    (X : Subgroup (pCore p G)) : Prop :=
  ∃ D : Subgroup (pCore p G), TBSGammaWitness (G := G) p A K X D

/-- A `Γ`-member of minimal cardinality. -/
@[expose]
public def CFSG.TBSGammaMinimal {G : Type u} [Group G] (p : ℕ) (A K : Subgroup G)
    (B : Subgroup (pCore p G)) : Prop :=
  TBSGamma (G := G) p A K B ∧
    ∀ X : Subgroup (pCore p G),
      TBSGamma (G := G) p A K X → Nat.card B ≤ Nat.card X

/-- A single critical witness makes the top subgroup of `O_p(G)` a `Γ`-member. -/
public theorem CFSG.thompson_bender_gamma_top_of_critical_witness
    {G : Type u} [Group G]
    {p : ℕ} {A K : Subgroup G} {D : Subgroup (pCore p G)}
    (hDchar : D.Characteristic)
    (hDcomm : ⁅D, ⊤⁆ ≤ centerIn (G := pCore p G) D)
    (hDclass : NilpotencyClassLe 2 (↥D))
    (hDexp : Monoid.exponent (↥D) = p)
    (hnorm :
      A ⊔ K ≤ Subgroup.normalizer
        ((D.map (pCore p G).subtype : Subgroup G) : Set G))
    (hnot :
      ¬ D.map (pCore p G).subtype ≤ Subgroup.centralizer (K : Set G)) :
    TBSGamma (G := G) p A K ⊤ := by
  refine ⟨D, ?_, hDchar, hDcomm, hDclass, hDexp, ?_⟩
  · intro x _hx
    exact trivial
  · exact ⟨hnorm, hnot⟩

/--
A `Γ` witness gives a concrete element of its critical subgroup not centralized
by `K`.
-/
public theorem CFSG.thompson_bender_gammaWitness_noncentralizing_pair
    {G : Type u} [Group G]
    {p : ℕ} {A K : Subgroup G} {X D : Subgroup (pCore p G)}
    (hD : TBSGammaWitness (G := G) p A K X D) :
    ∃ x : pCore p G, x ∈ D ∧ ∃ k : G, k ∈ K ∧ k * (x : G) ≠ (x : G) * k := by
  rcases hD with ⟨_hDX, _hDchar, _hDcomm, _hDclass, _hDexp, _hnorm, hnot⟩
  exact
    thompson_bender_exists_pCore_mem_noncentralizing_of_not_map_le_centralizer
      (G := G) (p := p) (D := D) (K := K) hnot

/-- A `Γ` member contains a concrete element not centralized by `K`. -/
public theorem CFSG.thompson_bender_gamma_noncentralizing_pair
    {G : Type u} [Group G]
    {p : ℕ} {A K : Subgroup G} {X : Subgroup (pCore p G)}
    (hX : TBSGamma (G := G) p A K X) :
    ∃ x : pCore p G, x ∈ X ∧ ∃ k : G, k ∈ K ∧ k * (x : G) ≠ (x : G) * k := by
  rcases hX with ⟨D, hD⟩
  rcases hD with ⟨hDX, _hDchar, _hDcomm, _hDclass, _hDexp, _hnorm, hnot⟩
  obtain ⟨x, hxD, k, hk, hne⟩ :=
    thompson_bender_exists_pCore_mem_noncentralizing_of_not_map_le_centralizer
      (G := G) (p := p) (D := D) (K := K) hnot
  exact ⟨x, hDX hxD, k, hk, hne⟩

/-- A `Γ` member gives a concrete non-fixed point for the conjugation action of `K`. -/
public theorem CFSG.thompson_bender_gamma_exists_nonfixed_action
    {G : Type u} [Group G]
    {p : ℕ} {A K : Subgroup G} {X : Subgroup (pCore p G)}
    (hX : TBSGamma (G := G) p A K X) :
    let P : Subgroup G := pCore p G
    let hKleNormP : K ≤ Subgroup.normalizer (P : Set G) :=
      Subgroup.le_normalizer_of_normal (H := P)
    let φ : K →* MulAut P :=
      (Subgroup.normalizerMonoidHom (H := P)).comp (Subgroup.inclusion hKleNormP)
    ∃ k : K, ∃ x : P, x ∈ X ∧ φ k x ≠ x := by
  obtain ⟨x, hxX, k, hk, hne⟩ :=
    thompson_bender_gamma_noncentralizing_pair
      (G := G) (p := p) (A := A) (K := K) hX
  let P : Subgroup G := pCore p G
  let hKleNormP : K ≤ Subgroup.normalizer (P : Set G) :=
    Subgroup.le_normalizer_of_normal (H := P)
  let φ : K →* MulAut P :=
    (Subgroup.normalizerMonoidHom (H := P)).comp (Subgroup.inclusion hKleNormP)
  change ∃ k : K, ∃ x : P, x ∈ X ∧ φ k x ≠ x
  refine ⟨⟨k, hk⟩, x, hxX, ?_⟩
  intro hfix
  have hconj : k * (x : G) * k⁻¹ = (x : G) := by
    simpa [φ, hKleNormP, P, Subgroup.normalizerMonoidHom_apply_apply_coe] using
      congrArg Subtype.val hfix
  have hcomm : k * (x : G) = (x : G) * k := by
    simpa [mul_assoc] using congrArg (fun t : G => t * k) hconj
  exact hne hcomm

/-- The conjugation action image of a `p'` subgroup has element orders coprime to `p`. -/
public theorem CFSG.thompson_bender_conjAction_order_coprime_of_card_coprime
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} {P K : Subgroup G} [P.Normal]
    (hKcop : Nat.Coprime p (Nat.card K)) (k : K) :
    let hKleNormP : K ≤ Subgroup.normalizer (P : Set G) :=
      Subgroup.le_normalizer_of_normal (H := P)
    let φ : K →* MulAut P :=
      (Subgroup.normalizerMonoidHom (H := P)).comp (Subgroup.inclusion hKleNormP)
    Nat.Coprime p (orderOf (φ k)) := by
  let hKleNormP : K ≤ Subgroup.normalizer (P : Set G) :=
    Subgroup.le_normalizer_of_normal (H := P)
  let φ : K →* MulAut P :=
    (Subgroup.normalizerMonoidHom (H := P)).comp (Subgroup.inclusion hKleNormP)
  change Nat.Coprime p (orderOf (φ k))
  exact Nat.Coprime.of_dvd_right
    ((orderOf_map_dvd (ψ := φ) k).trans (orderOf_dvd_natCard k)) hKcop

/-- A `Γ` member yields a nontrivial conjugation-action automorphism of p-prime order. -/
public theorem CFSG.thompson_bender_gamma_exists_nontrivial_conjAction_of_card_coprime
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} {A K : Subgroup G} {X : Subgroup (pCore p G)}
    (hKcop : Nat.Coprime p (Nat.card K))
    (hX : TBSGamma (G := G) p A K X) :
    let P : Subgroup G := pCore p G
    let hKleNormP : K ≤ Subgroup.normalizer (P : Set G) :=
      Subgroup.le_normalizer_of_normal (H := P)
    let φ : K →* MulAut P :=
      (Subgroup.normalizerMonoidHom (H := P)).comp (Subgroup.inclusion hKleNormP)
    ∃ k : K, φ k ≠ 1 ∧ Nat.Coprime p (orderOf (φ k)) := by
  obtain ⟨k, x, _hxX, hnonfix⟩ :=
    thompson_bender_gamma_exists_nonfixed_action
      (G := G) (p := p) (A := A) (K := K) hX
  let P : Subgroup G := pCore p G
  let hKleNormP : K ≤ Subgroup.normalizer (P : Set G) :=
    Subgroup.le_normalizer_of_normal (H := P)
  let φ : K →* MulAut P :=
    (Subgroup.normalizerMonoidHom (H := P)).comp (Subgroup.inclusion hKleNormP)
  change ∃ k : K, φ k ≠ 1 ∧ Nat.Coprime p (orderOf (φ k))
  refine ⟨k, ?_, ?_⟩
  · intro hkone
    have hfixx : φ k x = x := by
      simp [hkone]
    exact hnonfix (by simpa [φ, P, hKleNormP] using hfixx)
  · exact
      thompson_bender_conjAction_order_coprime_of_card_coprime
        (G := G) (p := p) (P := pCore p G) (K := K) hKcop k

/-- Every `Γ` member is nontrivial. -/
public theorem CFSG.thompson_bender_gamma_ne_bot
    {G : Type u} [Group G]
    {p : ℕ} {A K : Subgroup G} {X : Subgroup (pCore p G)}
    (hX : TBSGamma (G := G) p A K X) :
    X ≠ ⊥ := by
  obtain ⟨x, hxX, _k, _hk, hne⟩ :=
    thompson_bender_gamma_noncentralizing_pair
      (G := G) (p := p) (A := A) (K := K) hX
  intro hXbot
  have hxone : x = 1 := by
    have hxbot : x ∈ (⊥ : Subgroup (pCore p G)) := by
      simpa [hXbot] using hxX
    simpa using hxbot
  exact hne (by simp [hxone])

/-- A cardinal-minimal `Γ` member is nontrivial. -/
public theorem CFSG.thompson_bender_minimal_gamma_ne_bot
    {G : Type u} [Group G]
    {p : ℕ} {A K : Subgroup G} {B : Subgroup (pCore p G)}
    (hB : TBSGammaMinimal (G := G) p A K B) :
    B ≠ ⊥ :=
  thompson_bender_gamma_ne_bot (G := G) (p := p) (A := A) (K := K) hB.1

/-- A witness for `X ∈ Γ` also makes the witness subgroup itself a `Γ` member. -/
public theorem CFSG.thompson_bender_gamma_self_of_witness
    {G : Type u} [Group G]
    {p : ℕ} {A K : Subgroup G} {X D : Subgroup (pCore p G)}
    (hD : TBSGammaWitness (G := G) p A K X D) :
    TBSGamma (G := G) p A K D := by
  rcases hD with ⟨_hDX, hDchar, hDcomm, hDclass, hDexp, hnorm, hnot⟩
  refine ⟨D, ?_, hDchar, hDcomm, hDclass, hDexp, ?_⟩
  · intro x hx
    exact hx
  · exact ⟨hnorm, hnot⟩

/-- In a cardinal-minimal `Γ` member, every chosen `Γ` witness is the member itself. -/
public theorem CFSG.thompson_bender_minimal_gamma_eq_witness
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} {A K : Subgroup G} {B D : Subgroup (pCore p G)}
    (hB : TBSGammaMinimal (G := G) p A K B)
    (hD : TBSGammaWitness (G := G) p A K B D) :
    D = B := by
  rcases hD with ⟨hDB, hDchar, hDcomm, hDclass, hDexp, hnorm, hnot⟩
  have hDgamma : TBSGamma (G := G) p A K D := by
    refine ⟨D, ?_, hDchar, hDcomm, hDclass, hDexp, ?_⟩
    · intro x hx
      exact hx
    · exact ⟨hnorm, hnot⟩
  have hcard : Nat.card B ≤ Nat.card D := hB.2 D hDgamma
  exact Subgroup.eq_of_le_of_card_ge hDB hcard

/-- A minimal `Γ` member is characteristic in `O_p(G)`. -/
public theorem CFSG.thompson_bender_minimal_gamma_characteristic
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} {A K : Subgroup G} {B : Subgroup (pCore p G)}
    (hB : TBSGammaMinimal (G := G) p A K B) :
    B.Characteristic := by
  rcases hB.1 with ⟨D, hD⟩
  rcases hD with ⟨hDB, hDchar, hDcomm, hDclass, hDexp, hnorm, hnot⟩
  have hEq : D = B := by
    exact thompson_bender_minimal_gamma_eq_witness
      (G := G) (p := p) (A := A) (K := K)
      (B := B) (D := D) hB
      ⟨hDB, hDchar, hDcomm, hDclass, hDexp, hnorm, hnot⟩
  simpa [hEq] using hDchar

/-- The commutator condition transfers from a witness to a minimal `Γ` member. -/
public theorem CFSG.thompson_bender_minimal_gamma_commutator_le_centerIn
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} {A K : Subgroup G} {B : Subgroup (pCore p G)}
    (hB : TBSGammaMinimal (G := G) p A K B) :
    ⁅B, ⊤⁆ ≤ centerIn (G := pCore p G) B := by
  rcases hB.1 with ⟨D, hD⟩
  rcases hD with ⟨hDB, hDchar, hDcomm, hDclass, hDexp, hnorm, hnot⟩
  have hEq : D = B := by
    exact thompson_bender_minimal_gamma_eq_witness
      (G := G) (p := p) (A := A) (K := K)
      (B := B) (D := D) hB
      ⟨hDB, hDchar, hDcomm, hDclass, hDexp, hnorm, hnot⟩
  simpa [hEq] using hDcomm

/-- A minimal `Γ` member has nilpotency class at most two. -/
public theorem CFSG.thompson_bender_minimal_gamma_nilpotencyClassLe_two
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} {A K : Subgroup G} {B : Subgroup (pCore p G)}
    (hB : TBSGammaMinimal (G := G) p A K B) :
    NilpotencyClassLe 2 (↥B) := by
  rcases hB.1 with ⟨D, hD⟩
  rcases hD with ⟨hDB, hDchar, hDcomm, hDclass, hDexp, hnorm, hnot⟩
  have hEq : D = B := by
    exact thompson_bender_minimal_gamma_eq_witness
      (G := G) (p := p) (A := A) (K := K)
      (B := B) (D := D) hB
      ⟨hDB, hDchar, hDcomm, hDclass, hDexp, hnorm, hnot⟩
  subst B
  simpa using hDclass

/-- A minimal `Γ` member has exponent `p`. -/
public theorem CFSG.thompson_bender_minimal_gamma_exponent_eq
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} {A K : Subgroup G} {B : Subgroup (pCore p G)}
    (hB : TBSGammaMinimal (G := G) p A K B) :
    Monoid.exponent (↥B) = p := by
  rcases hB.1 with ⟨D, hD⟩
  rcases hD with ⟨hDB, hDchar, hDcomm, hDclass, hDexp, hnorm, hnot⟩
  have hEq : D = B := by
    exact thompson_bender_minimal_gamma_eq_witness
      (G := G) (p := p) (A := A) (K := K)
      (B := B) (D := D) hB
      ⟨hDB, hDchar, hDcomm, hDclass, hDexp, hnorm, hnot⟩
  subst B
  simpa using hDexp

/-- Nontrivial elements of a minimal `Γ` member have ambient order `p`. -/
public theorem CFSG.thompson_bender_minimal_gamma_orderOf_eq_p_of_ne_one
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {A K : Subgroup G} {B : Subgroup (pCore p G)}
    (hB : TBSGammaMinimal (G := G) p A K B)
    {x : pCore p G} (hxB : x ∈ B) (hxne : x ≠ 1) :
    orderOf (x : G) = p := by
  let xB : B := ⟨x, hxB⟩
  have hxBne : xB ≠ 1 := by
    intro hxB_one
    exact hxne (by simpa [xB] using congrArg Subtype.val hxB_one)
  have hxpowB : xB ^ p = 1 := by
    have hdiv : Monoid.exponent (↥B) ∣ p := by
      simp [thompson_bender_minimal_gamma_exponent_eq
        (G := G) (p := p) (A := A) (K := K) hB]
    exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hdiv xB
  have hxorderB : orderOf xB = p := orderOf_eq_prime hxpowB hxBne
  have hxorderP : orderOf x = p := by
    simpa [xB, Subgroup.orderOf_coe] using hxorderB
  simpa [Subgroup.orderOf_coe] using hxorderP

/--
Final-step endpoint for a minimal `Γ` member: a nontrivial element centralizing
`A` also centralizes `K`.
-/
public theorem CFSG.thompson_bender_minimal_gamma_mem_centralizer_A_centralizes_K
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {A K : Subgroup G} {B : Subgroup (pCore p G)}
    (hcent :
      ∀ x : G,
        x ∈ Subgroup.centralizer (A : Set G) → orderOf x = p → x ∈ A)
    (hA_norm_K : A ≤ Subgroup.normalizer (K : Set G))
    (hKcop : Nat.Coprime p (Nat.card K))
    (hB : TBSGammaMinimal (G := G) p A K B)
    {x : pCore p G} (hxB : x ∈ B) (hxne : x ≠ 1)
    (hxCentA : (x : G) ∈ Subgroup.centralizer (A : Set G)) :
    (x : G) ∈ Subgroup.centralizer (K : Set G) := by
  exact
    thompson_bender_order_p_pCore_mem_centralizer_A_centralizes_K
      (G := G) (p := p) (A := A) (K := K)
      hcent hA_norm_K hKcop x.property hxCentA
      (thompson_bender_minimal_gamma_orderOf_eq_p_of_ne_one
        (G := G) (p := p) (A := A) (K := K) (B := B) hB hxB hxne)

/--
Pointwise version of the final endpoint: such an element is fixed by the
conjugation action of every element of `K`.
-/
public theorem CFSG.thompson_bender_minimal_gamma_mem_centralizer_A_fixed_by_conjAction
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {A K : Subgroup G} {B : Subgroup (pCore p G)}
    (hcent :
      ∀ x : G,
        x ∈ Subgroup.centralizer (A : Set G) → orderOf x = p → x ∈ A)
    (hA_norm_K : A ≤ Subgroup.normalizer (K : Set G))
    (hKcop : Nat.Coprime p (Nat.card K))
    (hB : TBSGammaMinimal (G := G) p A K B)
    {x : pCore p G} (hxB : x ∈ B) (hxne : x ≠ 1)
    (hxCentA : (x : G) ∈ Subgroup.centralizer (A : Set G)) :
    let P : Subgroup G := pCore p G
    let hKleNormP : K ≤ Subgroup.normalizer (P : Set G) :=
      Subgroup.le_normalizer_of_normal (H := P)
    let φ : K →* MulAut P :=
      (Subgroup.normalizerMonoidHom (H := P)).comp (Subgroup.inclusion hKleNormP)
    ∀ k : K, φ k x = x := by
  let P : Subgroup G := pCore p G
  let hKleNormP : K ≤ Subgroup.normalizer (P : Set G) :=
    Subgroup.le_normalizer_of_normal (H := P)
  let φ : K →* MulAut P :=
    (Subgroup.normalizerMonoidHom (H := P)).comp (Subgroup.inclusion hKleNormP)
  change ∀ k : K, φ k x = x
  intro k
  have hxCentK : (x : G) ∈ Subgroup.centralizer (K : Set G) :=
    thompson_bender_minimal_gamma_mem_centralizer_A_centralizes_K
      (G := G) (p := p) (A := A) (K := K) (B := B)
      hcent hA_norm_K hKcop hB hxB hxne hxCentA
  have hcomm : (k : G) * (x : G) = (x : G) * (k : G) := by
    simpa using
      (Subgroup.mem_centralizer_iff.mp hxCentK (k : G) k.property)
  have hconj : (k : G) * (x : G) * (k : G)⁻¹ = (x : G) := by
    simpa [mul_assoc] using congrArg (fun t : G => t * (k : G)⁻¹) hcomm
  apply Subtype.ext
  simpa [φ, hKleNormP, P, Subgroup.normalizerMonoidHom_apply_apply_coe] using hconj

/-- The ambient image of a minimal `Γ` member is normalized by `A ⊔ K`. -/
public theorem CFSG.thompson_bender_minimal_gamma_le_normalizer
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} {A K : Subgroup G} {B : Subgroup (pCore p G)}
    (hB : TBSGammaMinimal (G := G) p A K B) :
    A ⊔ K ≤ Subgroup.normalizer
      (((B.map (pCore p G).subtype : Subgroup G) : Set G)) := by
  rcases hB.1 with ⟨D, hD⟩
  rcases hD with ⟨hDB, hDchar, hDcomm, hDclass, hDexp, hnorm, hnot⟩
  have hEq : D = B := by
    exact thompson_bender_minimal_gamma_eq_witness
      (G := G) (p := p) (A := A) (K := K)
      (B := B) (D := D) hB
      ⟨hDB, hDchar, hDcomm, hDclass, hDexp, hnorm, hnot⟩
  subst B
  simpa using hnorm

/-- `A` normalizes the ambient image of a minimal `Γ` member. -/
public theorem CFSG.thompson_bender_minimal_gamma_A_le_normalizer
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} {A K : Subgroup G} {B : Subgroup (pCore p G)}
    (hB : TBSGammaMinimal (G := G) p A K B) :
    A ≤ Subgroup.normalizer
      (((B.map (pCore p G).subtype : Subgroup G) : Set G)) :=
  le_trans le_sup_left
    (thompson_bender_minimal_gamma_le_normalizer
      (G := G) (p := p) (A := A) (K := K) (B := B) hB)

/-- `K` normalizes the ambient image of a minimal `Γ` member. -/
public theorem CFSG.thompson_bender_minimal_gamma_K_le_normalizer
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} {A K : Subgroup G} {B : Subgroup (pCore p G)}
    (hB : TBSGammaMinimal (G := G) p A K B) :
    K ≤ Subgroup.normalizer
      (((B.map (pCore p G).subtype : Subgroup G) : Set G)) :=
  le_trans le_sup_right
    (thompson_bender_minimal_gamma_le_normalizer
      (G := G) (p := p) (A := A) (K := K) (B := B) hB)

/-- Conjugating an element of `K` by an element of `A` stays in `K` when `A ≤ N_G(K)`. -/
public def CFSG.thompson_bender_conjKOfANormalizes
    {G : Type u} [Group G] {A K : Subgroup G}
    (hA_norm_K : A ≤ Subgroup.normalizer (K : Set G))
    (a : A) (k : K) : K :=
  ⟨(a : G) * (k : G) * (a : G)⁻¹, by
    have haNorm : (a : G) ∈ Subgroup.normalizer (K : Set G) := hA_norm_K a.2
    rw [Subgroup.mem_normalizer_iff] at haNorm
    exact (haNorm (k : G)).1 k.2⟩

/--
Compatibility of the induced conjugation actions: applying `a ∈ A` after
`k ∈ K` is the same as first applying `a`, then the conjugate `a k a⁻¹ ∈ K`.
-/
public theorem CFSG.thompson_bender_pCore_conjAction_A_comp_K_eq_conjK
    {G : Type u} [Group G]
    {p : ℕ} {A K : Subgroup G}
    (hA_norm_K : A ≤ Subgroup.normalizer (K : Set G))
    (a : A) (k : K) (x : pCore p G) :
    let P : Subgroup G := pCore p G
    let hAleNormP : A ≤ Subgroup.normalizer (P : Set G) :=
      Subgroup.le_normalizer_of_normal (H := P)
    let φA : A →* MulAut P :=
      (Subgroup.normalizerMonoidHom (H := P)).comp (Subgroup.inclusion hAleNormP)
    let hKleNormP : K ≤ Subgroup.normalizer (P : Set G) :=
      Subgroup.le_normalizer_of_normal (H := P)
    let φK : K →* MulAut P :=
      (Subgroup.normalizerMonoidHom (H := P)).comp (Subgroup.inclusion hKleNormP)
    φA a (φK k x) =
      φK (thompson_bender_conjKOfANormalizes (G := G) hA_norm_K a k) (φA a x) := by
  let P : Subgroup G := pCore p G
  let hAleNormP : A ≤ Subgroup.normalizer (P : Set G) :=
    Subgroup.le_normalizer_of_normal (H := P)
  let φA : A →* MulAut P :=
    (Subgroup.normalizerMonoidHom (H := P)).comp (Subgroup.inclusion hAleNormP)
  let hKleNormP : K ≤ Subgroup.normalizer (P : Set G) :=
    Subgroup.le_normalizer_of_normal (H := P)
  let φK : K →* MulAut P :=
    (Subgroup.normalizerMonoidHom (H := P)).comp (Subgroup.inclusion hKleNormP)
  change φA a (φK k x) =
    φK (thompson_bender_conjKOfANormalizes (G := G) hA_norm_K a k) (φA a x)
  apply Subtype.ext
  have hconj :
      (a : G) * ((k : G) * (x : G) * (k : G)⁻¹) * (a : G)⁻¹ =
        ((a : G) * (k : G) * (a : G)⁻¹) *
          ((a : G) * (x : G) * (a : G)⁻¹) *
            (((a : G) * (k : G) * (a : G)⁻¹)⁻¹) := by
    group
  simpa [φA, φK, hAleNormP, hKleNormP, P,
    thompson_bender_conjKOfANormalizes,
    Subgroup.normalizerMonoidHom_apply_apply_coe] using hconj

/--
If a subgroup normalizes the ambient image of `B ≤ O_p(G)`, its induced
conjugation action on `O_p(G)` preserves `B`.
-/
public theorem CFSG.thompson_bender_pCore_subgroup_conjAction_mem_of_le_normalizer
    {G : Type u} [Group G]
    {p : ℕ} {L : Subgroup G} {B : Subgroup (pCore p G)}
    (hL_norm_B :
      L ≤ Subgroup.normalizer
        (((B.map (pCore p G).subtype : Subgroup G) : Set G)))
    (l : L) {x : pCore p G} (hxB : x ∈ B) :
    let P : Subgroup G := pCore p G
    let hLleNormP : L ≤ Subgroup.normalizer (P : Set G) :=
      Subgroup.le_normalizer_of_normal (H := P)
    let φ : L →* MulAut P :=
      (Subgroup.normalizerMonoidHom (H := P)).comp (Subgroup.inclusion hLleNormP)
    φ l x ∈ B := by
  let P : Subgroup G := pCore p G
  let hLleNormP : L ≤ Subgroup.normalizer (P : Set G) :=
    Subgroup.le_normalizer_of_normal (H := P)
  let φ : L →* MulAut P :=
    (Subgroup.normalizerMonoidHom (H := P)).comp (Subgroup.inclusion hLleNormP)
  change φ l x ∈ B
  have hxMap : (x : G) ∈ B.map (pCore p G).subtype :=
    Subgroup.mem_map.mpr ⟨x, hxB, rfl⟩
  have hlNorm :
      (l : G) ∈ Subgroup.normalizer
        (((B.map (pCore p G).subtype : Subgroup G) : Set G)) :=
    hL_norm_B l.property
  have hconjMap :
      (l : G) * (x : G) * (l : G)⁻¹ ∈ B.map (pCore p G).subtype :=
    (Subgroup.mem_normalizer_iff.mp hlNorm (x : G)).1 hxMap
  rcases Subgroup.mem_map.mp hconjMap with ⟨y, hyB, hy_eq⟩
  have hval : ((φ l x : P) : G) = (y : G) := by
    calc
      ((φ l x : P) : G) = (l : G) * (x : G) * (l : G)⁻¹ := by
        simp [φ, P, Subgroup.normalizerMonoidHom_apply_apply_coe]
      _ = (y : G) := by simpa using hy_eq.symm
  have hφeq : φ l x = y := Subtype.ext hval
  simpa [hφeq] using hyB

/-- The induced conjugation action of `A` preserves a minimal `Γ` member. -/
public theorem CFSG.thompson_bender_minimal_gamma_A_conjAction_mem
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} {A K : Subgroup G} {B : Subgroup (pCore p G)}
    (hB : TBSGammaMinimal (G := G) p A K B)
    (a : A) {x : pCore p G} (hxB : x ∈ B) :
    let P : Subgroup G := pCore p G
    let hAleNormP : A ≤ Subgroup.normalizer (P : Set G) :=
      Subgroup.le_normalizer_of_normal (H := P)
    let φ : A →* MulAut P :=
      (Subgroup.normalizerMonoidHom (H := P)).comp (Subgroup.inclusion hAleNormP)
    φ a x ∈ B :=
  thompson_bender_pCore_subgroup_conjAction_mem_of_le_normalizer
    (G := G) (p := p) (L := A) (B := B)
    (thompson_bender_minimal_gamma_A_le_normalizer
      (G := G) (p := p) (A := A) (K := K) (B := B) hB) a hxB

/-- The induced conjugation action of `K` preserves a minimal `Γ` member. -/
public theorem CFSG.thompson_bender_minimal_gamma_K_conjAction_mem
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} {A K : Subgroup G} {B : Subgroup (pCore p G)}
    (hB : TBSGammaMinimal (G := G) p A K B)
    (k : K) {x : pCore p G} (hxB : x ∈ B) :
    let P : Subgroup G := pCore p G
    let hKleNormP : K ≤ Subgroup.normalizer (P : Set G) :=
      Subgroup.le_normalizer_of_normal (H := P)
    let φ : K →* MulAut P :=
      (Subgroup.normalizerMonoidHom (H := P)).comp (Subgroup.inclusion hKleNormP)
    φ k x ∈ B :=
  thompson_bender_pCore_subgroup_conjAction_mem_of_le_normalizer
    (G := G) (p := p) (L := K) (B := B)
    (thompson_bender_minimal_gamma_K_le_normalizer
      (G := G) (p := p) (A := A) (K := K) (B := B) hB) k hxB

/--
If an element of a minimal `Γ` member is fixed by the conjugation action of
`A`, then it is fixed by the conjugation action of `K`.
-/
public theorem CFSG.thompson_bender_minimal_gamma_fixed_by_A_fixed_by_K
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {A K : Subgroup G} {B : Subgroup (pCore p G)}
    (hcent :
      ∀ x : G,
        x ∈ Subgroup.centralizer (A : Set G) → orderOf x = p → x ∈ A)
    (hA_norm_K : A ≤ Subgroup.normalizer (K : Set G))
    (hKcop : Nat.Coprime p (Nat.card K))
    (hB : TBSGammaMinimal (G := G) p A K B)
    {x : pCore p G} (hxB : x ∈ B) (hxne : x ≠ 1)
    (hxFixedA :
      let P : Subgroup G := pCore p G
      let hAleNormP : A ≤ Subgroup.normalizer (P : Set G) :=
        Subgroup.le_normalizer_of_normal (H := P)
      let ψ : A →* MulAut P :=
        (Subgroup.normalizerMonoidHom (H := P)).comp (Subgroup.inclusion hAleNormP)
      ∀ a : A, ψ a x = x) :
    let P : Subgroup G := pCore p G
    let hKleNormP : K ≤ Subgroup.normalizer (P : Set G) :=
      Subgroup.le_normalizer_of_normal (H := P)
    let φ : K →* MulAut P :=
      (Subgroup.normalizerMonoidHom (H := P)).comp (Subgroup.inclusion hKleNormP)
    ∀ k : K, φ k x = x := by
  let P : Subgroup G := pCore p G
  let hAleNormP : A ≤ Subgroup.normalizer (P : Set G) :=
    Subgroup.le_normalizer_of_normal (H := P)
  let ψ : A →* MulAut P :=
    (Subgroup.normalizerMonoidHom (H := P)).comp (Subgroup.inclusion hAleNormP)
  let hKleNormP : K ≤ Subgroup.normalizer (P : Set G) :=
    Subgroup.le_normalizer_of_normal (H := P)
  let φ : K →* MulAut P :=
    (Subgroup.normalizerMonoidHom (H := P)).comp (Subgroup.inclusion hKleNormP)
  change ∀ k : K, φ k x = x
  change ∀ a : A, ψ a x = x at hxFixedA
  have hxCentA : (x : G) ∈ Subgroup.centralizer (A : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    let aA : A := ⟨a, ha⟩
    have hfix : ψ aA x = x := hxFixedA aA
    have hconj : a * (x : G) * a⁻¹ = (x : G) := by
      simpa [ψ, aA, hAleNormP, P, Subgroup.normalizerMonoidHom_apply_apply_coe] using
        congrArg Subtype.val hfix
    simpa [mul_assoc] using congrArg (fun t : G => t * a) hconj
  exact
    thompson_bender_minimal_gamma_mem_centralizer_A_fixed_by_conjAction
      (G := G) (p := p) (A := A) (K := K) (B := B)
      hcent hA_norm_K hKcop hB hxB hxne hxCentA

/--
Pointwise bridge between ambient centralizer membership and fixedness under the
conjugation action induced on `O_p(G)`.
-/
public theorem CFSG.thompson_bender_pCore_mem_centralizer_iff_fixed_by_conjAction
    {G : Type u} [Group G]
    {p : ℕ} {L : Subgroup G} {x : pCore p G} :
    (x : G) ∈ Subgroup.centralizer (L : Set G) ↔
      let P : Subgroup G := pCore p G
      let hLleNormP : L ≤ Subgroup.normalizer (P : Set G) :=
        Subgroup.le_normalizer_of_normal (H := P)
      let φ : L →* MulAut P :=
        (Subgroup.normalizerMonoidHom (H := P)).comp (Subgroup.inclusion hLleNormP)
      ∀ l : L, φ l x = x := by
  constructor
  · intro hxCent
    let P : Subgroup G := pCore p G
    let hLleNormP : L ≤ Subgroup.normalizer (P : Set G) :=
      Subgroup.le_normalizer_of_normal (H := P)
    let φ : L →* MulAut P :=
      (Subgroup.normalizerMonoidHom (H := P)).comp (Subgroup.inclusion hLleNormP)
    change ∀ l : L, φ l x = x
    intro l
    have hcomm : (l : G) * (x : G) = (x : G) * (l : G) := by
      simpa using
        (Subgroup.mem_centralizer_iff.mp hxCent (l : G) l.property)
    have hconj : (l : G) * (x : G) * (l : G)⁻¹ = (x : G) := by
      simpa [mul_assoc] using congrArg (fun t : G => t * (l : G)⁻¹) hcomm
    apply Subtype.ext
    simpa [φ, hLleNormP, P, Subgroup.normalizerMonoidHom_apply_apply_coe] using hconj
  · intro hfix
    let P : Subgroup G := pCore p G
    let hLleNormP : L ≤ Subgroup.normalizer (P : Set G) :=
      Subgroup.le_normalizer_of_normal (H := P)
    let φ : L →* MulAut P :=
      (Subgroup.normalizerMonoidHom (H := P)).comp (Subgroup.inclusion hLleNormP)
    change ∀ l : L, φ l x = x at hfix
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have hconj : l * (x : G) * l⁻¹ = (x : G) := by
      simpa [φ, hLleNormP, P, Subgroup.normalizerMonoidHom_apply_apply_coe] using
        congrArg Subtype.val (hfix ⟨l, hl⟩)
    simpa [mul_assoc] using congrArg (fun t : G => t * l) hconj

/--
Invariant-subgroup form of
`thompson_bender_pCore_subgroup_conjAction_mem_of_le_normalizer`.
-/
public theorem CFSG.thompson_bender_pCore_subgroup_conjAction_isInvariant_of_le_normalizer
    {G : Type u} [Group G]
    {p : ℕ} {L : Subgroup G} {B : Subgroup (pCore p G)}
    (hL_norm_B :
      L ≤ Subgroup.normalizer
        (((B.map (pCore p G).subtype : Subgroup G) : Set G))) :
    let P : Subgroup G := pCore p G
    let hLleNormP : L ≤ Subgroup.normalizer (P : Set G) :=
      Subgroup.le_normalizer_of_normal (H := P)
    let φ : L →* MulAut P :=
      (Subgroup.normalizerMonoidHom (H := P)).comp (Subgroup.inclusion hLleNormP)
    letI : MulDistribMulAction L P := MulDistribMulAction.compHom P φ
    IsInvariant L P B := by
  let P : Subgroup G := pCore p G
  let hLleNormP : L ≤ Subgroup.normalizer (P : Set G) :=
    Subgroup.le_normalizer_of_normal (H := P)
  let φ : L →* MulAut P :=
    (Subgroup.normalizerMonoidHom (H := P)).comp (Subgroup.inclusion hLleNormP)
  let : MulDistribMulAction L P := MulDistribMulAction.compHom P φ
  change IsInvariant L P B
  refine ⟨?_⟩
  intro l x
  constructor
  · intro hx
    change φ l x ∈ B
    exact thompson_bender_pCore_subgroup_conjAction_mem_of_le_normalizer
      (G := G) (p := p) (L := L) (B := B) hL_norm_B l hx
  · intro hx
    change φ l x ∈ B at hx
    have hpre : φ l⁻¹ (φ l x) ∈ B :=
      thompson_bender_pCore_subgroup_conjAction_mem_of_le_normalizer
        (G := G) (p := p) (L := L) (B := B) hL_norm_B l⁻¹ hx
    simpa using hpre

/-- The induced conjugation action of `A` leaves a minimal `Γ` member invariant. -/
public theorem CFSG.thompson_bender_minimal_gamma_A_conjAction_isInvariant
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} {A K : Subgroup G} {B : Subgroup (pCore p G)}
    (hB : TBSGammaMinimal (G := G) p A K B) :
    let P : Subgroup G := pCore p G
    let hAleNormP : A ≤ Subgroup.normalizer (P : Set G) :=
      Subgroup.le_normalizer_of_normal (H := P)
    let φ : A →* MulAut P :=
      (Subgroup.normalizerMonoidHom (H := P)).comp (Subgroup.inclusion hAleNormP)
    letI : MulDistribMulAction A P := MulDistribMulAction.compHom P φ
    IsInvariant A P B :=
  thompson_bender_pCore_subgroup_conjAction_isInvariant_of_le_normalizer
    (G := G) (p := p) (L := A) (B := B)
    (thompson_bender_minimal_gamma_A_le_normalizer
      (G := G) (p := p) (A := A) (K := K) (B := B) hB)

/-- The induced conjugation action of `K` leaves a minimal `Γ` member invariant. -/
public theorem CFSG.thompson_bender_minimal_gamma_K_conjAction_isInvariant
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} {A K : Subgroup G} {B : Subgroup (pCore p G)}
    (hB : TBSGammaMinimal (G := G) p A K B) :
    let P : Subgroup G := pCore p G
    let hKleNormP : K ≤ Subgroup.normalizer (P : Set G) :=
      Subgroup.le_normalizer_of_normal (H := P)
    let φ : K →* MulAut P :=
      (Subgroup.normalizerMonoidHom (H := P)).comp (Subgroup.inclusion hKleNormP)
    letI : MulDistribMulAction K P := MulDistribMulAction.compHom P φ
    IsInvariant K P B :=
  thompson_bender_pCore_subgroup_conjAction_isInvariant_of_le_normalizer
    (G := G) (p := p) (L := K) (B := B)
    (thompson_bender_minimal_gamma_K_le_normalizer
      (G := G) (p := p) (A := A) (K := K) (B := B) hB)

/--
Fixed-point-subgroup form of
`thompson_bender_pCore_mem_centralizer_iff_fixed_by_conjAction`.
-/
public theorem CFSG.thompson_bender_pCore_mem_centralizer_iff_mem_fixedPointSubgroup
    {G : Type u} [Group G]
    {p : ℕ} {L : Subgroup G} {x : pCore p G} :
    let P : Subgroup G := pCore p G
    let hLleNormP : L ≤ Subgroup.normalizer (P : Set G) :=
      Subgroup.le_normalizer_of_normal (H := P)
    let φ : L →* MulAut P :=
      (Subgroup.normalizerMonoidHom (H := P)).comp (Subgroup.inclusion hLleNormP)
    letI : MulDistribMulAction L P := MulDistribMulAction.compHom P φ
    (x : G) ∈ Subgroup.centralizer (L : Set G) ↔ x ∈ fixedPointSubgroup L P := by
  let P : Subgroup G := pCore p G
  let hLleNormP : L ≤ Subgroup.normalizer (P : Set G) :=
    Subgroup.le_normalizer_of_normal (H := P)
  let φ : L →* MulAut P :=
    (Subgroup.normalizerMonoidHom (H := P)).comp (Subgroup.inclusion hLleNormP)
  let : MulDistribMulAction L P := MulDistribMulAction.compHom P φ
  change (x : G) ∈ Subgroup.centralizer (L : Set G) ↔ x ∈ fixedPointSubgroup L P
  rw [thompson_bender_pCore_mem_centralizer_iff_fixed_by_conjAction
    (G := G) (p := p) (L := L) (x := x)]
  constructor
  · intro hfix
    change ∀ l : L, φ l x = x at hfix
    rw [FixedPoints.mem_subgroup]
    intro l
    simpa [MulAction.compHom_smul_def] using hfix l
  · intro hx
    rw [FixedPoints.mem_subgroup] at hx
    change ∀ l : L, φ l x = x
    intro l
    simpa [MulAction.compHom_smul_def] using hx l

/-- Membership in `B ∩ fixedPointSubgroup` is the same as membership in
`B` plus ambient centralization of the acting subgroup. -/
public theorem CFSG.thompson_bender_pCore_mem_inf_fixedPointSubgroup_iff
    {G : Type u} [Group G]
    {p : ℕ} {L : Subgroup G} {B : Subgroup (pCore p G)} {x : pCore p G} :
    let P : Subgroup G := pCore p G
    let hLleNormP : L ≤ Subgroup.normalizer (P : Set G) :=
      Subgroup.le_normalizer_of_normal (H := P)
    let φ : L →* MulAut P :=
      (Subgroup.normalizerMonoidHom (H := P)).comp (Subgroup.inclusion hLleNormP)
    letI : MulDistribMulAction L P := MulDistribMulAction.compHom P φ
    x ∈ B ⊓ fixedPointSubgroup L P ↔
      x ∈ B ∧ (x : G) ∈ Subgroup.centralizer (L : Set G) := by
  let P : Subgroup G := pCore p G
  let hLleNormP : L ≤ Subgroup.normalizer (P : Set G) :=
    Subgroup.le_normalizer_of_normal (H := P)
  let φ : L →* MulAut P :=
    (Subgroup.normalizerMonoidHom (H := P)).comp (Subgroup.inclusion hLleNormP)
  let : MulDistribMulAction L P := MulDistribMulAction.compHom P φ
  change x ∈ B ⊓ fixedPointSubgroup L P ↔
      x ∈ B ∧ (x : G) ∈ Subgroup.centralizer (L : Set G)
  constructor
  · intro hx
    exact ⟨hx.1,
      (thompson_bender_pCore_mem_centralizer_iff_mem_fixedPointSubgroup
        (G := G) (p := p) (L := L) (x := x)).mpr hx.2⟩
  · intro hx
    exact ⟨hx.1,
      (thompson_bender_pCore_mem_centralizer_iff_mem_fixedPointSubgroup
        (G := G) (p := p) (L := L) (x := x)).mp hx.2⟩

/--
Extracts the element-level centralizer witness from a nontrivial
`B ∩ fixedPointSubgroup`.
-/
public theorem CFSG.thompson_bender_pCore_exists_nontrivial_mem_centralizer_of_inf_fixedPointSubgroup_ne_bot
    {G : Type u} [Group G]
    {p : ℕ} {L : Subgroup G} {B : Subgroup (pCore p G)}
    (hNontr :
      (let P : Subgroup G := pCore p G
       let hLleNormP : L ≤ Subgroup.normalizer (P : Set G) :=
          Subgroup.le_normalizer_of_normal (H := P)
       let φ : L →* MulAut P :=
          (Subgroup.normalizerMonoidHom (H := P)).comp (Subgroup.inclusion hLleNormP)
       letI : MulDistribMulAction L P := MulDistribMulAction.compHom P φ
       B ⊓ fixedPointSubgroup L P) ≠ ⊥) :
    ∃ u : pCore p G,
      u ∈ B ∧ u ≠ 1 ∧ (u : G) ∈ Subgroup.centralizer (L : Set G) := by
  let P : Subgroup G := pCore p G
  let hLleNormP : L ≤ Subgroup.normalizer (P : Set G) :=
    Subgroup.le_normalizer_of_normal (H := P)
  let φ : L →* MulAut P :=
    (Subgroup.normalizerMonoidHom (H := P)).comp (Subgroup.inclusion hLleNormP)
  let : MulDistribMulAction L P := MulDistribMulAction.compHom P φ
  change B ⊓ fixedPointSubgroup L P ≠ ⊥ at hNontr
  rcases Subgroup.ne_bot_iff_exists_ne_one.mp hNontr with ⟨u, hu_ne⟩
  have hu :
      (u : P) ∈ B ∧ (u : G) ∈ Subgroup.centralizer (L : Set G) :=
    (thompson_bender_pCore_mem_inf_fixedPointSubgroup_iff
      (G := G) (p := p) (L := L) (B := B) (x := (u : P))).mp u.property
  refine ⟨u, hu.1, ?_, hu.2⟩
  intro hu_one
  exact hu_ne (Subtype.ext hu_one)

/--
A finite `p`-group of operators on a nontrivial finite `p`-group has a
nontrivial fixed point.
-/
public theorem CFSG.thompson_bender_exists_nontrivial_mem_fixedPointSubgroup_of_pgroup_action
    {P A : Type*} [Group P] [Finite P] [Group A] [Finite A]
    {p : ℕ} [Fact p.Prime] [MulDistribMulAction A P]
    (hP : IsPGroup p P) (hA : IsPGroup p A) [Nontrivial P] :
    ∃ x : P, x ∈ fixedPointSubgroup A P ∧ x ≠ 1 := by
  classical
  have hdiv : p ∣ Nat.card P := by
    obtain ⟨n, hnpos, hcard⟩ :=
      (IsPGroup.nontrivial_iff_card (p := p) (G := P) (hG := hP)).mp inferInstance
    rw [hcard]
    exact dvd_pow_self p (ne_of_gt hnpos)
  have hone : (1 : P) ∈ MulAction.fixedPoints A P := by
    simp [MulAction.mem_fixedPoints]
  obtain ⟨x, hxfix, hxne⟩ :=
    hA.exists_fixed_point_of_prime_dvd_card_of_fixed_point
      (α := P) hdiv hone
  refine ⟨x, ?_, ?_⟩
  · simpa [fixedPointSubgroup, FixedPoints.mem_subgroup] using
      MulAction.mem_fixedPoints.mp hxfix
  · intro hx
    exact hxne hx.symm

/--
Subgroup form of the p-group fixed-point extraction: an invariant nontrivial
`p`-subgroup has nontrivial intersection with the ambient fixed-point subgroup.
-/
public theorem CFSG.thompson_bender_inf_fixedPointSubgroup_ne_bot_of_pgroup_action
    {P A : Type*} [Group P] [Finite P] [Group A] [Finite A]
    {p : ℕ} [Fact p.Prime] [MulDistribMulAction A P]
    (B : Subgroup P) [IsInvariant A P B]
    (hB : IsPGroup p B) (hA : IsPGroup p A) (hBne : B ≠ ⊥) :
    B ⊓ fixedPointSubgroup A P ≠ ⊥ := by
  classical
  let : MulDistribMulAction A B := {
    smul a x :=
      ⟨a • (x : P),
        (IsInvariant.invariant (A := A) (G := P) (H := B) a (x : P)).1 x.2⟩
    one_smul x := by
      ext
      change ((1 : A) • (x : P)) = x
      simp
    mul_smul a b x := by
      ext
      change ((a * b) • (x : P)) = a • (b • (x : P))
      simpa using (mul_smul a b (x : P))
    smul_mul a x y := by
      ext
      change a • ((x : P) * (y : P)) = a • (x : P) * a • (y : P)
      simp
    smul_one a := by
      ext
      change a • (1 : P) = (1 : P)
      simp }
  have : Nontrivial B := (Subgroup.nontrivial_iff_ne_bot B).2 hBne
  obtain ⟨x, hxfix, hxne⟩ :=
    thompson_bender_exists_nontrivial_mem_fixedPointSubgroup_of_pgroup_action
      (P := B) (A := A) (p := p) hB hA
  refine Subgroup.ne_bot_iff_exists_ne_one.mpr ?_
  refine ⟨⟨(x : P), ?_⟩, ?_⟩
  · constructor
    · exact x.2
    · change (x : P) ∈ fixedPointSubgroup A P
      rw [FixedPoints.mem_subgroup]
      intro a
      have hxfix_a : a • x = x :=
        (FixedPoints.mem_subgroup (M := A) (a := x)).1 hxfix a
      exact congrArg Subtype.val hxfix_a
  · intro hx
    apply hxne
    apply Subtype.ext
    simpa using congrArg Subtype.val hx

/--
A nonfixed point for the induced `K` action gives a nontrivial displacement
element inside the minimal `Γ` member.
-/
public theorem CFSG.thompson_bender_minimal_gamma_exists_nontrivial_conjAction_displacement
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} {A K : Subgroup G} {B : Subgroup (pCore p G)}
    (hB : TBSGammaMinimal (G := G) p A K B) :
    let P : Subgroup G := pCore p G
    let hKleNormP : K ≤ Subgroup.normalizer (P : Set G) :=
      Subgroup.le_normalizer_of_normal (H := P)
    let φ : K →* MulAut P :=
      (Subgroup.normalizerMonoidHom (H := P)).comp (Subgroup.inclusion hKleNormP)
    ∀ k : K, ∀ x : P, x ∈ B → φ k x ≠ x →
      ∃ c : P, c ∈ B ∧ c ≠ 1 ∧ c = φ k x * x⁻¹ := by
  let P : Subgroup G := pCore p G
  let hKleNormP : K ≤ Subgroup.normalizer (P : Set G) :=
    Subgroup.le_normalizer_of_normal (H := P)
  let φ : K →* MulAut P :=
    (Subgroup.normalizerMonoidHom (H := P)).comp (Subgroup.inclusion hKleNormP)
  change ∀ k : K, ∀ x : P, x ∈ B → φ k x ≠ x →
      ∃ c : P, c ∈ B ∧ c ≠ 1 ∧ c = φ k x * x⁻¹
  intro k x hxB hxnonfix
  refine ⟨φ k x * x⁻¹, ?_, ?_, rfl⟩
  · exact B.mul_mem
      (thompson_bender_minimal_gamma_K_conjAction_mem
        (G := G) (p := p) (A := A) (K := K) (B := B) hB k hxB)
      (B.inv_mem hxB)
  · intro hdisp
    exact hxnonfix (mul_inv_eq_one.mp hdisp)

/--
The subgroup generated by displacement elements `φ k x * x⁻¹` for a fixed
induced `K`-action element.
-/
@[expose]
public def CFSG.TBSConjActionDisplacementSubgroup
    {G : Type u} [Group G]
    (p : ℕ) (K : Subgroup G) (B : Subgroup (pCore p G)) (k : K) :
    Subgroup (pCore p G) := by
  let P : Subgroup G := pCore p G
  let hKleNormP : K ≤ Subgroup.normalizer (P : Set G) :=
    Subgroup.le_normalizer_of_normal (H := P)
  let φ : K →* MulAut P :=
    (Subgroup.normalizerMonoidHom (H := P)).comp (Subgroup.inclusion hKleNormP)
  exact Subgroup.closure {c : P | ∃ x : P, x ∈ B ∧ c = φ k x * x⁻¹}

/-- The fixed-`k` displacement subgroup is a `p`-group inside `O_p(G)`. -/
public theorem CFSG.thompson_bender_conjAction_displacementSubgroup_isPGroup
    {G : Type u} [Group G]
    {p : ℕ} {K : Subgroup G} {B : Subgroup (pCore p G)} (k : K) :
    IsPGroup p (TBSConjActionDisplacementSubgroup (G := G) p K B k) :=
  (pCore_isPGroup (G := G) (p := p)).to_subgroup
    (TBSConjActionDisplacementSubgroup (G := G) p K B k)

/-- The subgroup generated by all displacement elements `φ k x * x⁻¹`, for `k ∈ K`. -/
@[expose]
public def CFSG.TBSConjActionDisplacementSubgroupAll
    {G : Type u} [Group G]
    (p : ℕ) (K : Subgroup G) (B : Subgroup (pCore p G)) :
    Subgroup (pCore p G) := by
  let P : Subgroup G := pCore p G
  let hKleNormP : K ≤ Subgroup.normalizer (P : Set G) :=
    Subgroup.le_normalizer_of_normal (H := P)
  let φ : K →* MulAut P :=
    (Subgroup.normalizerMonoidHom (H := P)).comp (Subgroup.inclusion hKleNormP)
  exact Subgroup.closure {c : P | ∃ k : K, ∃ x : P, x ∈ B ∧ c = φ k x * x⁻¹}

/-- The fixed-`k` displacement subgroup lies in the all-`K` displacement subgroup. -/
public theorem CFSG.thompson_bender_conjAction_displacementSubgroup_le_all
    {G : Type u} [Group G]
    {p : ℕ} {K : Subgroup G} {B : Subgroup (pCore p G)} (k : K) :
    TBSConjActionDisplacementSubgroup (G := G) p K B k ≤
      TBSConjActionDisplacementSubgroupAll (G := G) p K B := by
  let P : Subgroup G := pCore p G
  let hKleNormP : K ≤ Subgroup.normalizer (P : Set G) :=
    Subgroup.le_normalizer_of_normal (H := P)
  let φ : K →* MulAut P :=
    (Subgroup.normalizerMonoidHom (H := P)).comp (Subgroup.inclusion hKleNormP)
  rw [TBSConjActionDisplacementSubgroup, TBSConjActionDisplacementSubgroupAll,
    Subgroup.closure_le]
  intro c hc
  rcases hc with ⟨x, hxB, rfl⟩
  exact Subgroup.subset_closure ⟨k, x, hxB, rfl⟩

/-- The all-`K` displacement subgroup is a `p`-group inside `O_p(G)`. -/
public theorem CFSG.thompson_bender_conjAction_displacementSubgroupAll_isPGroup
    {G : Type u} [Group G]
    {p : ℕ} {K : Subgroup G} {B : Subgroup (pCore p G)} :
    IsPGroup p (TBSConjActionDisplacementSubgroupAll (G := G) p K B) :=
  (pCore_isPGroup (G := G) (p := p)).to_subgroup
    (TBSConjActionDisplacementSubgroupAll (G := G) p K B)

/-- The fixed-`k` displacement subgroup of a minimal `Γ` member lies in `B`. -/
public theorem CFSG.thompson_bender_minimal_gamma_displacementSubgroup_le
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} {A K : Subgroup G} {B : Subgroup (pCore p G)}
    (hB : TBSGammaMinimal (G := G) p A K B) (k : K) :
    TBSConjActionDisplacementSubgroup (G := G) p K B k ≤ B := by
  let P : Subgroup G := pCore p G
  let hKleNormP : K ≤ Subgroup.normalizer (P : Set G) :=
    Subgroup.le_normalizer_of_normal (H := P)
  let φ : K →* MulAut P :=
    (Subgroup.normalizerMonoidHom (H := P)).comp (Subgroup.inclusion hKleNormP)
  rw [TBSConjActionDisplacementSubgroup, Subgroup.closure_le]
  intro c hc
  rcases hc with ⟨x, hxB, rfl⟩
  exact B.mul_mem
    (thompson_bender_minimal_gamma_K_conjAction_mem
      (G := G) (p := p) (A := A) (K := K) (B := B) hB k hxB)
    (B.inv_mem hxB)

/-- The all-`K` displacement subgroup of a minimal `Γ` member lies in `B`. -/
public theorem CFSG.thompson_bender_minimal_gamma_displacementSubgroupAll_le
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} {A K : Subgroup G} {B : Subgroup (pCore p G)}
    (hB : TBSGammaMinimal (G := G) p A K B) :
    TBSConjActionDisplacementSubgroupAll (G := G) p K B ≤ B := by
  let P : Subgroup G := pCore p G
  let hKleNormP : K ≤ Subgroup.normalizer (P : Set G) :=
    Subgroup.le_normalizer_of_normal (H := P)
  let φ : K →* MulAut P :=
    (Subgroup.normalizerMonoidHom (H := P)).comp (Subgroup.inclusion hKleNormP)
  rw [TBSConjActionDisplacementSubgroupAll, Subgroup.closure_le]
  intro c hc
  rcases hc with ⟨k, x, hxB, rfl⟩
  exact B.mul_mem
    (thompson_bender_minimal_gamma_K_conjAction_mem
      (G := G) (p := p) (A := A) (K := K) (B := B) hB k hxB)
    (B.inv_mem hxB)

/-- If `B` is invariant under the induced `K` action, the all-`K`
displacement subgroup lies in `B`. -/
public theorem CFSG.thompson_bender_conjAction_displacementSubgroupAll_le_of_isInvariant
    {G : Type u} [Group G]
    {p : ℕ} {K : Subgroup G} {B : Subgroup (pCore p G)}
    (hInv :
      let P : Subgroup G := pCore p G
      let hKleNormP : K ≤ Subgroup.normalizer (P : Set G) :=
        Subgroup.le_normalizer_of_normal (H := P)
      let φ : K →* MulAut P :=
        (Subgroup.normalizerMonoidHom (H := P)).comp (Subgroup.inclusion hKleNormP)
      letI : MulDistribMulAction K P := MulDistribMulAction.compHom P φ
      IsInvariant K P B) :
    TBSConjActionDisplacementSubgroupAll (G := G) p K B ≤ B := by
  let P : Subgroup G := pCore p G
  let hKleNormP : K ≤ Subgroup.normalizer (P : Set G) :=
    Subgroup.le_normalizer_of_normal (H := P)
  let φ : K →* MulAut P :=
    (Subgroup.normalizerMonoidHom (H := P)).comp (Subgroup.inclusion hKleNormP)
  let : MulDistribMulAction K P := MulDistribMulAction.compHom P φ
  change IsInvariant K P B at hInv
  let : IsInvariant K P B := hInv
  rw [TBSConjActionDisplacementSubgroupAll, Subgroup.closure_le]
  intro c hc
  rcases hc with ⟨k, x, hxB, rfl⟩
  exact B.mul_mem
    ((IsInvariant.invariant (A := K) (G := P) (H := B) k x).1 hxB)
    (B.inv_mem hxB)

/--
The all-`K` displacement subgroup maps into the usual action commutator
subgroup of a `K`-invariant subgroup `B`.
-/
public theorem CFSG.thompson_bender_conjAction_displacementSubgroupAll_le_commutatorAction_map_subtype_of_isInvariant
    {G : Type u} [Group G]
    {p : ℕ} {K : Subgroup G} {B : Subgroup (pCore p G)}
    (hInv :
      let P : Subgroup G := pCore p G
      let hKleNormP : K ≤ Subgroup.normalizer (P : Set G) :=
        Subgroup.le_normalizer_of_normal (H := P)
      let φ : K →* MulAut P :=
        (Subgroup.normalizerMonoidHom (H := P)).comp (Subgroup.inclusion hKleNormP)
      letI : MulDistribMulAction K P := MulDistribMulAction.compHom P φ
      IsInvariant K P B) :
    (let P : Subgroup G := pCore p G
     let hKleNormP : K ≤ Subgroup.normalizer (P : Set G) :=
        Subgroup.le_normalizer_of_normal (H := P)
     let φ : K →* MulAut P :=
        (Subgroup.normalizerMonoidHom (H := P)).comp (Subgroup.inclusion hKleNormP)
     letI : MulDistribMulAction K P := MulDistribMulAction.compHom P φ
     letI : IsInvariant K P B := hInv
     TBSConjActionDisplacementSubgroupAll (G := G) p K B ≤
        (commutatorAction (A := K) (G := B)).map B.subtype) := by
  let P : Subgroup G := pCore p G
  let hKleNormP : K ≤ Subgroup.normalizer (P : Set G) :=
    Subgroup.le_normalizer_of_normal (H := P)
  let φ : K →* MulAut P :=
    (Subgroup.normalizerMonoidHom (H := P)).comp (Subgroup.inclusion hKleNormP)
  let : MulDistribMulAction K P := MulDistribMulAction.compHom P φ
  change IsInvariant K P B at hInv
  let : IsInvariant K P B := hInv
  let C : Subgroup B := commutatorAction (A := K) (G := B)
  have hCnorm : C.Normal := by
    simpa [C] using (commutatorAction_normal (G := B) (A := K))
  rw [TBSConjActionDisplacementSubgroupAll, Subgroup.closure_le]
  intro c hc
  rcases hc with ⟨k, x, hxB, rfl⟩
  let xb : B := ⟨x, hxB⟩
  let yb : B := k • xb
  have hstd : xb⁻¹ * yb ∈ C := by
    change xb⁻¹ * yb ∈ commutatorAction (A := K) (G := B)
    rw [commutatorAction_eq_closure]
    exact Subgroup.subset_closure ⟨k, xb, rfl⟩
  have hconj : yb * (xb⁻¹ * yb) * yb⁻¹ ∈ C :=
    Subgroup.Normal.conj_mem hCnorm (xb⁻¹ * yb) hstd yb
  refine Subgroup.mem_map.mpr ⟨yb * (xb⁻¹ * yb) * yb⁻¹, hconj, ?_⟩
  have hyb_val : (yb : P) = φ k x := by
    change k • (x : P) = φ k x
    exact MulAction.compHom_smul_def φ k x
  change ((yb * (xb⁻¹ * yb) * yb⁻¹ : B) : P) = φ k x * x⁻¹
  simp [xb, yb, hyb_val, mul_assoc]

/-- A nonfixed point makes the fixed-`k` displacement subgroup nontrivial. -/
public theorem CFSG.thompson_bender_conjAction_displacementSubgroup_ne_bot_of_nonfixed
    {G : Type u} [Group G]
    {p : ℕ} {K : Subgroup G} {B : Subgroup (pCore p G)} :
    let P : Subgroup G := pCore p G
    let hKleNormP : K ≤ Subgroup.normalizer (P : Set G) :=
      Subgroup.le_normalizer_of_normal (H := P)
    let φ : K →* MulAut P :=
      (Subgroup.normalizerMonoidHom (H := P)).comp (Subgroup.inclusion hKleNormP)
    ∀ k : K, ∀ x : P, x ∈ B → φ k x ≠ x →
      TBSConjActionDisplacementSubgroup (G := G) p K B k ≠ ⊥ := by
  let P : Subgroup G := pCore p G
  let hKleNormP : K ≤ Subgroup.normalizer (P : Set G) :=
    Subgroup.le_normalizer_of_normal (H := P)
  let φ : K →* MulAut P :=
    (Subgroup.normalizerMonoidHom (H := P)).comp (Subgroup.inclusion hKleNormP)
  change ∀ k : K, ∀ x : P, x ∈ B → φ k x ≠ x →
      TBSConjActionDisplacementSubgroup (G := G) p K B k ≠ ⊥
  intro k x hxB hxnonfix
  refine Subgroup.ne_bot_iff_exists_ne_one.mpr ?_
  refine ⟨⟨φ k x * x⁻¹, ?_⟩, ?_⟩
  · rw [TBSConjActionDisplacementSubgroup]
    exact Subgroup.subset_closure ⟨x, hxB, rfl⟩
  · intro hdisp
    exact hxnonfix (mul_inv_eq_one.mp (Subtype.ext_iff.mp hdisp))

/-- A nonfixed point makes the all-`K` displacement subgroup nontrivial. -/
public theorem CFSG.thompson_bender_conjAction_displacementSubgroupAll_ne_bot_of_nonfixed
    {G : Type u} [Group G]
    {p : ℕ} {K : Subgroup G} {B : Subgroup (pCore p G)} :
    let P : Subgroup G := pCore p G
    let hKleNormP : K ≤ Subgroup.normalizer (P : Set G) :=
      Subgroup.le_normalizer_of_normal (H := P)
    let φ : K →* MulAut P :=
      (Subgroup.normalizerMonoidHom (H := P)).comp (Subgroup.inclusion hKleNormP)
    ∀ k : K, ∀ x : P, x ∈ B → φ k x ≠ x →
      TBSConjActionDisplacementSubgroupAll (G := G) p K B ≠ ⊥ := by
  let P : Subgroup G := pCore p G
  let hKleNormP : K ≤ Subgroup.normalizer (P : Set G) :=
    Subgroup.le_normalizer_of_normal (H := P)
  let φ : K →* MulAut P :=
    (Subgroup.normalizerMonoidHom (H := P)).comp (Subgroup.inclusion hKleNormP)
  change ∀ k : K, ∀ x : P, x ∈ B → φ k x ≠ x →
      TBSConjActionDisplacementSubgroupAll (G := G) p K B ≠ ⊥
  intro k x hxB hxnonfix hAllBot
  have hfixed_ne :
      TBSConjActionDisplacementSubgroup (G := G) p K B k ≠ ⊥ :=
    thompson_bender_conjAction_displacementSubgroup_ne_bot_of_nonfixed
      (G := G) (p := p) (K := K) (B := B) k x hxB hxnonfix
  have hlebot :
      TBSConjActionDisplacementSubgroup (G := G) p K B k ≤ ⊥ := by
    simpa [hAllBot] using
      thompson_bender_conjAction_displacementSubgroup_le_all
        (G := G) (p := p) (K := K) (B := B) k
  exact hfixed_ne (le_bot_iff.mp hlebot)

/--
The all-`K` displacement subgroup is stable under one element of the induced
`A` action, provided `A` normalizes `K` and preserves `B`.
-/
public theorem CFSG.thompson_bender_conjAction_displacementSubgroupAll_A_mem
    {G : Type u} [Group G]
    {p : ℕ} {A K : Subgroup G} {B : Subgroup (pCore p G)}
    (hA_norm_K : A ≤ Subgroup.normalizer (K : Set G))
    (hBInv :
      let P : Subgroup G := pCore p G
      let hAleNormP : A ≤ Subgroup.normalizer (P : Set G) :=
        Subgroup.le_normalizer_of_normal (H := P)
      let φA : A →* MulAut P :=
        (Subgroup.normalizerMonoidHom (H := P)).comp (Subgroup.inclusion hAleNormP)
      letI : MulDistribMulAction A P := MulDistribMulAction.compHom P φA
      IsInvariant A P B)
    (a : A) {c : pCore p G}
    (hc : c ∈ TBSConjActionDisplacementSubgroupAll (G := G) p K B) :
    let P : Subgroup G := pCore p G
    let hAleNormP : A ≤ Subgroup.normalizer (P : Set G) :=
      Subgroup.le_normalizer_of_normal (H := P)
    let φA : A →* MulAut P :=
      (Subgroup.normalizerMonoidHom (H := P)).comp (Subgroup.inclusion hAleNormP)
    φA a c ∈ TBSConjActionDisplacementSubgroupAll (G := G) p K B := by
  let P : Subgroup G := pCore p G
  let hAleNormP : A ≤ Subgroup.normalizer (P : Set G) :=
    Subgroup.le_normalizer_of_normal (H := P)
  let φA : A →* MulAut P :=
    (Subgroup.normalizerMonoidHom (H := P)).comp (Subgroup.inclusion hAleNormP)
  let hKleNormP : K ≤ Subgroup.normalizer (P : Set G) :=
    Subgroup.le_normalizer_of_normal (H := P)
  let φK : K →* MulAut P :=
    (Subgroup.normalizerMonoidHom (H := P)).comp (Subgroup.inclusion hKleNormP)
  let : MulDistribMulAction A P := MulDistribMulAction.compHom P φA
  change IsInvariant A P B at hBInv
  let : IsInvariant A P B := hBInv
  change φA a c ∈ TBSConjActionDisplacementSubgroupAll (G := G) p K B
  let S : Set P := {c : P | ∃ k : K, ∃ x : P, x ∈ B ∧ c = φK k x * x⁻¹}
  rw [TBSConjActionDisplacementSubgroupAll] at hc ⊢
  change c ∈ Subgroup.closure S at hc
  change φA a c ∈ Subgroup.closure S
  refine Subgroup.closure_induction
    (p := fun y _ => φA a y ∈ Subgroup.closure S) (x := c)
    ?_ ?_ ?_ ?_ hc
  · intro y hy
    change ∃ k : K, ∃ x : P, x ∈ B ∧ y = φK k x * x⁻¹ at hy
    rcases hy with ⟨k, x, hxB, rfl⟩
    have hxB' : φA a x ∈ B :=
      (IsInvariant.invariant (A := A) (G := P) (H := B) a x).1 hxB
    let k' : K := thompson_bender_conjKOfANormalizes (G := G) hA_norm_K a k
    have hcomp : φA a (φK k x) = φK k' (φA a x) := by
      simpa [P, φA, φK, hAleNormP, hKleNormP, k'] using
        thompson_bender_pCore_conjAction_A_comp_K_eq_conjK
          (G := G) (p := p) (A := A) (K := K) hA_norm_K a k x
    have hgen :
        φA a (φK k x * x⁻¹) = φK k' (φA a x) * (φA a x)⁻¹ := by
      simp [hcomp]
    exact Subgroup.subset_closure ⟨k', φA a x, hxB', hgen⟩
  · simp
  · intro x y _ _ hx hy
    simpa using (Subgroup.mul_mem (Subgroup.closure S) hx hy)
  · intro x _ hx
    simpa using (Subgroup.inv_mem (Subgroup.closure S) hx)

/--
The all-`K` displacement subgroup is invariant under the induced `A` action
when `A` normalizes `K` and preserves `B`.
-/
public theorem CFSG.thompson_bender_conjAction_displacementSubgroupAll_A_isInvariant
    {G : Type u} [Group G]
    {p : ℕ} {A K : Subgroup G} {B : Subgroup (pCore p G)}
    (hA_norm_K : A ≤ Subgroup.normalizer (K : Set G))
    (hBInv :
      let P : Subgroup G := pCore p G
      let hAleNormP : A ≤ Subgroup.normalizer (P : Set G) :=
        Subgroup.le_normalizer_of_normal (H := P)
      let φA : A →* MulAut P :=
        (Subgroup.normalizerMonoidHom (H := P)).comp (Subgroup.inclusion hAleNormP)
      letI : MulDistribMulAction A P := MulDistribMulAction.compHom P φA
      IsInvariant A P B) :
    let P : Subgroup G := pCore p G
    let hAleNormP : A ≤ Subgroup.normalizer (P : Set G) :=
      Subgroup.le_normalizer_of_normal (H := P)
    let φA : A →* MulAut P :=
      (Subgroup.normalizerMonoidHom (H := P)).comp (Subgroup.inclusion hAleNormP)
    letI : MulDistribMulAction A P := MulDistribMulAction.compHom P φA
    IsInvariant A P (TBSConjActionDisplacementSubgroupAll (G := G) p K B) := by
  let P : Subgroup G := pCore p G
  let hAleNormP : A ≤ Subgroup.normalizer (P : Set G) :=
    Subgroup.le_normalizer_of_normal (H := P)
  let φA : A →* MulAut P :=
    (Subgroup.normalizerMonoidHom (H := P)).comp (Subgroup.inclusion hAleNormP)
  let : MulDistribMulAction A P := MulDistribMulAction.compHom P φA
  change IsInvariant A P (TBSConjActionDisplacementSubgroupAll (G := G) p K B)
  refine ⟨?_⟩
  intro a x
  constructor
  · intro hx
    change φA a x ∈ TBSConjActionDisplacementSubgroupAll (G := G) p K B
    exact
      thompson_bender_conjAction_displacementSubgroupAll_A_mem
        (G := G) (p := p) (A := A) (K := K) (B := B)
        hA_norm_K hBInv a hx
  · intro hx
    change φA a x ∈ TBSConjActionDisplacementSubgroupAll (G := G) p K B at hx
    have hpre :
        φA a⁻¹ (φA a x) ∈
          TBSConjActionDisplacementSubgroupAll (G := G) p K B :=
      thompson_bender_conjAction_displacementSubgroupAll_A_mem
        (G := G) (p := p) (A := A) (K := K) (B := B)
        hA_norm_K hBInv a⁻¹ hx
    simpa using hpre

/-- The all-`K` displacement subgroup of a minimal `Γ` member is `K`-invariant. -/
public theorem CFSG.thompson_bender_minimal_gamma_displacementSubgroupAll_K_isInvariant
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} {A K : Subgroup G} {B : Subgroup (pCore p G)}
    (hB : TBSGammaMinimal (G := G) p A K B) :
    let P : Subgroup G := pCore p G
    let hKleNormP : K ≤ Subgroup.normalizer (P : Set G) :=
      Subgroup.le_normalizer_of_normal (H := P)
    let φK : K →* MulAut P :=
      (Subgroup.normalizerMonoidHom (H := P)).comp (Subgroup.inclusion hKleNormP)
    letI : MulDistribMulAction K P := MulDistribMulAction.compHom P φK
    IsInvariant K P (TBSConjActionDisplacementSubgroupAll (G := G) p K B) := by
  exact
    thompson_bender_conjAction_displacementSubgroupAll_A_isInvariant
      (G := G) (p := p) (A := K) (K := K) (B := B)
      (Subgroup.le_normalizer (H := K))
      (thompson_bender_minimal_gamma_K_conjAction_isInvariant
        (G := G) (p := p) (A := A) (K := K) (B := B) hB)

/--
Direct intersection form of coprime action on an abelian group: the fixed
points meet the action commutator subgroup trivially.
-/
public theorem CFSG.thompson_bender_fixedPointSubgroup_inf_commutatorAction_eq_bot_of_solvable_coprime_comm
    {P A : Type*} [Group P] [Finite P] [Group A] [Finite A]
    [MulDistribMulAction A P]
    (hsolv : Group.IsSolvable P) (hcoprime : Nat.Coprime (Nat.card A) (Nat.card P))
    (hcomm : IsMulCommutative P) :
    fixedPointSubgroup A P ⊓ commutatorAction (A := A) (G := P) = ⊥ := by
  have hcompl :
      IsCompl (fixedPointSubgroup A P) (commutatorAction (A := A) (G := P)) :=
    proposition_1_6_d (G := P) (A := A) hsolv hcoprime hcomm
  exact (disjoint_iff).1 hcompl.disjoint

/-- The induced action on an invariant subgroup, packaged for local use. -/
@[reducible]
public def CFSG.thompson_bender_subgroupMulDistribMulActionOfIsInvariant
    {A P : Type u} [Group A] [Group P] [MulDistribMulAction A P]
    (B : Subgroup P) [IsInvariant A P B] :
    MulDistribMulAction A B where
  smul a x :=
    ⟨a • (x : P), (IsInvariant.invariant (A := A) (G := P) (H := B) a (x : P)).1 x.2⟩
  one_smul x := by
    ext
    change (1 : A) • (x : P) = x
    simp
  mul_smul a b x := by
    ext
    change (a * b) • (x : P) = a • b • (x : P)
    simp [mul_smul]
  smul_mul a x y := by
    ext
    change a • ((x : P) * (y : P)) = a • (x : P) * a • (y : P)
    simp
  smul_one a := by
    ext
    change a • (1 : P) = 1
    simp

/-- Baer's odd class-two abelian model: same elements, twisted multiplication. -/
public structure CFSG.TBSBaer (r : ℕ) (G : Type u) where
  val : G

namespace CFSG.TBSBaer

public instance {r : ℕ} {G : Type u} : CoeOut (TBSBaer r G) G where
  coe x := x.val

@[simp] public theorem ext_iff {r : ℕ} {G : Type u} {x y : TBSBaer r G} :
    x = y ↔ x.val = y.val := by
  constructor
  · intro h
    cases h
    rfl
  · intro h
    cases x
    cases y
    simp at h
    simp [h]

@[expose]
public def mul {r : ℕ} {G : Type u} [Group G] (x y : TBSBaer r G) : TBSBaer r G :=
  ⟨x.val * y.val * ⁅y.val, x.val⁆ ^ r⟩

@[expose]
public def one {r : ℕ} {G : Type u} [One G] : TBSBaer r G := ⟨1⟩

@[expose]
public def inv {r : ℕ} {G : Type u} [Inv G] (x : TBSBaer r G) : TBSBaer r G := ⟨x.val⁻¹⟩

public instance {r : ℕ} {G : Type u} [Group G] : Mul (TBSBaer r G) where
  mul := TBSBaer.mul

public instance {r : ℕ} {G : Type u} [One G] : One (TBSBaer r G) where
  one := TBSBaer.one

public instance {r : ℕ} {G : Type u} [Inv G] : Inv (TBSBaer r G) where
  inv := TBSBaer.inv

@[simp] public theorem coe_mul {r : ℕ} {G : Type u} [Group G] (x y : TBSBaer r G) :
    ((x * y : TBSBaer r G) : G) = (x : G) * (y : G) * ⁅(y : G), (x : G)⁆ ^ r := rfl

@[simp] public theorem coe_one {r : ℕ} {G : Type u} [One G] :
    ((1 : TBSBaer r G) : G) = (1 : G) := rfl

@[simp] public theorem coe_inv {r : ℕ} {G : Type u} [Inv G] (x : TBSBaer r G) :
    ((x⁻¹ : TBSBaer r G) : G) = ((x : G)⁻¹ : G) := rfl

public theorem commutator_mem_center_of_commutator_le_center
    {G : Type u} [Group G]
    (hcomm : _root_.commutator G ≤ Subgroup.center G) (x y : G) :
    ⁅x, y⁆ ∈ Subgroup.center G := by
  exact hcomm <|
    Subgroup.commutator_mem_commutator (H₁ := (⊤ : Subgroup G)) (H₂ := (⊤ : Subgroup G))
      (show x ∈ (⊤ : Subgroup G) by trivial) (show y ∈ (⊤ : Subgroup G) by trivial)

public theorem swap_mul_commutator_of_mem_center {G : Type u} [Group G] {x y : G}
    (hcomm : ⁅y, x⁆ ∈ Subgroup.center G) :
    y * x = x * y * ⁅y, x⁆ := by
  have hx : x * ⁅y, x⁆ = ⁅y, x⁆ * x := (Subgroup.mem_center_iff.mp hcomm) x
  have hy : y * ⁅y, x⁆ = ⁅y, x⁆ * y := (Subgroup.mem_center_iff.mp hcomm) y
  calc
    y * x = ⁅y, x⁆ * x * y := by
      simp [commutatorElement_def, mul_assoc]
    _ = x * ⁅y, x⁆ * y := by
      rw [← hx, mul_assoc]
    _ = x * (⁅y, x⁆ * y) := by
      simp [mul_assoc]
    _ = x * (y * ⁅y, x⁆) := by
      rw [← hy]
    _ = x * y * ⁅y, x⁆ := by
      simp [mul_assoc]

public theorem commutator_mul_right_of_commutator_le_center
    {G : Type u} [Group G]
    (hcomm : _root_.commutator G ≤ Subgroup.center G) (x y z : G) :
    ⁅x, y * z⁆ = ⁅x, y⁆ * ⁅x, z⁆ := by
  have hzcent : ⁅x, z⁆ ∈ Subgroup.center G :=
    commutator_mem_center_of_commutator_le_center hcomm x z
  have hzy : y * ⁅x, z⁆ = ⁅x, z⁆ * y :=
    (Subgroup.mem_center_iff.mp hzcent y)
  calc
    ⁅x, y * z⁆ = ⁅x, y⁆ * y * ⁅x, z⁆ * y⁻¹ := by
      rw [commutator_mul_right]
    _ = ⁅x, y⁆ * (y * ⁅x, z⁆) * y⁻¹ := by simp [mul_assoc]
    _ = ⁅x, y⁆ * (⁅x, z⁆ * y) * y⁻¹ := by rw [hzy]
    _ = ⁅x, y⁆ * ⁅x, z⁆ := by simp [mul_assoc]

public theorem commutator_mul_left_of_commutator_le_center
    {G : Type u} [Group G]
    (hcomm : _root_.commutator G ≤ Subgroup.center G) (x y z : G) :
    ⁅x * y, z⁆ = ⁅x, z⁆ * ⁅y, z⁆ := by
  have hycent : ⁅y, z⁆ ∈ Subgroup.center G :=
    commutator_mem_center_of_commutator_le_center hcomm y z
  have hxcent : ⁅x, z⁆ ∈ Subgroup.center G :=
    commutator_mem_center_of_commutator_le_center hcomm x z
  have hxy : x * ⁅y, z⁆ = ⁅y, z⁆ * x :=
    (Subgroup.mem_center_iff.mp hycent x)
  have hyx : ⁅y, z⁆ * ⁅x, z⁆ = ⁅x, z⁆ * ⁅y, z⁆ :=
    (Subgroup.mem_center_iff.mp hycent ⁅x, z⁆).symm
  calc
    ⁅x * y, z⁆ = x * ⁅y, z⁆ * x⁻¹ * ⁅x, z⁆ := by
      rw [commutator_mul_left]
    _ = ⁅y, z⁆ * ⁅x, z⁆ := by
      rw [hxy]
      simp [mul_assoc]
    _ = ⁅x, z⁆ * ⁅y, z⁆ := hyx

public theorem commutator_eq_one_of_right_mem_center
    {G : Type u} [Group G] {x z : G} (hz : z ∈ Subgroup.center G) :
    ⁅x, z⁆ = 1 := by
  exact commutatorElement_eq_one_iff_mul_comm.mpr
    ((Subgroup.mem_center_iff.mp hz x))

public theorem commutator_eq_one_of_left_mem_center
    {G : Type u} [Group G] {z x : G} (hz : z ∈ Subgroup.center G) :
    ⁅z, x⁆ = 1 := by
  exact commutatorElement_eq_one_iff_mul_comm.mpr
    ((Subgroup.mem_center_iff.mp hz x).symm)

public theorem commutator_right_baer_factor
    {G : Type u} [Group G] {r : ℕ}
    (hcomm : _root_.commutator G ≤ Subgroup.center G) (x y z : G) :
    ⁅z, x * y * ⁅y, x⁆ ^ r⁆ = ⁅z, x⁆ * ⁅z, y⁆ := by
  let c : G := ⁅y, x⁆
  have hc : c ∈ Subgroup.center G :=
    commutator_mem_center_of_commutator_le_center hcomm y x
  have hcpow : c ^ r ∈ Subgroup.center G := (Subgroup.center G).pow_mem hc r
  calc
    ⁅z, x * y * c ^ r⁆ = ⁅z, x * y⁆ * ⁅z, c ^ r⁆ := by
      rw [commutator_mul_right_of_commutator_le_center hcomm]
    _ = ⁅z, x * y⁆ := by
      rw [commutator_eq_one_of_right_mem_center hcpow]
      simp
    _ = ⁅z, x⁆ * ⁅z, y⁆ := by
      rw [commutator_mul_right_of_commutator_le_center hcomm]

public theorem commutator_left_baer_factor
    {G : Type u} [Group G] {r : ℕ}
    (hcomm : _root_.commutator G ≤ Subgroup.center G) (x y z : G) :
    ⁅y * z * ⁅z, y⁆ ^ r, x⁆ = ⁅y, x⁆ * ⁅z, x⁆ := by
  let c : G := ⁅z, y⁆
  have hc : c ∈ Subgroup.center G :=
    commutator_mem_center_of_commutator_le_center hcomm z y
  have hcpow : c ^ r ∈ Subgroup.center G := (Subgroup.center G).pow_mem hc r
  calc
    ⁅y * z * c ^ r, x⁆ = ⁅y * z, x⁆ * ⁅c ^ r, x⁆ := by
      rw [commutator_mul_left_of_commutator_le_center hcomm]
    _ = ⁅y * z, x⁆ := by
      rw [commutator_eq_one_of_left_mem_center hcpow]
      simp
    _ = ⁅y, x⁆ * ⁅z, x⁆ := by
      rw [commutator_mul_left_of_commutator_le_center hcomm]

public theorem center_three_mul_rotate {G : Type u} [Group G] {a b c : G}
    (ha : a ∈ Subgroup.center G) (hb : b ∈ Subgroup.center G)
    (hc : c ∈ Subgroup.center G) :
    a * (b * c) = c * (a * b) := by
  let aZ : Subgroup.center G := ⟨a, ha⟩
  let bZ : Subgroup.center G := ⟨b, hb⟩
  let cZ : Subgroup.center G := ⟨c, hc⟩
  have h : aZ * (bZ * cZ) = cZ * (aZ * bZ) := by
    simp [mul_assoc, mul_comm]
  exact congrArg Subtype.val h

public theorem mul_assoc_of_commutator_le_center
    {G : Type u} [Group G] {r : ℕ}
    (hcomm : _root_.commutator G ≤ Subgroup.center G)
    (x y z : TBSBaer r G) :
    (x * y) * z = x * (y * z) := by
  apply (ext_iff (G := G)).2
  let a : G := x.val
  let b : G := y.val
  let c : G := z.val
  let cba : G := ⁅b, a⁆
  let cca : G := ⁅c, a⁆
  let ccb : G := ⁅c, b⁆
  have hcba : cba ^ r ∈ Subgroup.center G :=
    (Subgroup.center G).pow_mem
      (commutator_mem_center_of_commutator_le_center hcomm b a) r
  have hcca : cca ^ r ∈ Subgroup.center G :=
    (Subgroup.center G).pow_mem
      (commutator_mem_center_of_commutator_le_center hcomm c a) r
  have hccb : ccb ^ r ∈ Subgroup.center G :=
    (Subgroup.center G).pow_mem
      (commutator_mem_center_of_commutator_le_center hcomm c b) r
  have hpow_zxzy :
      (cca * ccb) ^ r = cca ^ r * ccb ^ r := by
    exact (show Commute cca ccb from
      Subgroup.mem_center_iff.mp
        (commutator_mem_center_of_commutator_le_center hcomm c a) ccb |>.symm).mul_pow r
  have hpow_yxzx :
      (cba * cca) ^ r = cba ^ r * cca ^ r := by
    exact (show Commute cba cca from
      Subgroup.mem_center_iff.mp
        (commutator_mem_center_of_commutator_le_center hcomm b a) cca |>.symm).mul_pow r
  have hleft :
      (((x * y) * z : TBSBaer r G) : G) =
        a * b * c * (cba ^ r * (cca ^ r * ccb ^ r)) := by
    calc
      (((x * y) * z : TBSBaer r G) : G)
          = (a * b * cba ^ r) * c *
              ⁅c, a * b * cba ^ r⁆ ^ r := rfl
      _ = (a * b * cba ^ r) * c * (cca * ccb) ^ r := by
        rw [commutator_right_baer_factor (r := r) hcomm a b c]
      _ = (a * b * cba ^ r) * c * (cca ^ r * ccb ^ r) := by
        rw [hpow_zxzy]
      _ = a * b * c * (cba ^ r * (cca ^ r * ccb ^ r)) := by
        have hmove : cba ^ r * c = c * cba ^ r :=
          (Subgroup.mem_center_iff.mp hcba c).symm
        rw [show (a * b * cba ^ r) * c = a * b * c * cba ^ r by
          calc
            (a * b * cba ^ r) * c = a * b * (cba ^ r * c) := by simp [mul_assoc]
            _ = a * b * (c * cba ^ r) := by rw [hmove]
            _ = a * b * c * cba ^ r := by simp [mul_assoc]]
        simp [mul_assoc]
  have hright :
      ((x * (y * z) : TBSBaer r G) : G) =
        a * b * c * (ccb ^ r * (cba ^ r * cca ^ r)) := by
    calc
      ((x * (y * z) : TBSBaer r G) : G)
          = a * (b * c * ccb ^ r) *
              ⁅b * c * ccb ^ r, a⁆ ^ r := rfl
      _ = a * (b * c * ccb ^ r) * (cba * cca) ^ r := by
        rw [commutator_left_baer_factor (r := r) hcomm a b c]
      _ = a * (b * c * ccb ^ r) * (cba ^ r * cca ^ r) := by
        rw [hpow_yxzx]
      _ = a * b * c * (ccb ^ r * (cba ^ r * cca ^ r)) := by
        simp [mul_assoc]
  rw [hleft, hright]
  congr 1
  exact center_three_mul_rotate hcba hcca hccb

public theorem one_mul {G : Type u} [Group G] {r : ℕ} (x : TBSBaer r G) :
    (1 : TBSBaer r G) * x = x := by
  apply (ext_iff (G := G)).2
  simp

public theorem mul_one {G : Type u} [Group G] {r : ℕ} (x : TBSBaer r G) :
    x * (1 : TBSBaer r G) = x := by
  apply (ext_iff (G := G)).2
  simp

public theorem inv_mul_cancel {G : Type u} [Group G] {r : ℕ} (x : TBSBaer r G) :
    x⁻¹ * x = (1 : TBSBaer r G) := by
  apply (ext_iff (G := G)).2
  simp [commutatorElement_def]

@[reducible]
public def group {G : Type u} [Group G] {r : ℕ}
    (hcomm : _root_.commutator G ≤ Subgroup.center G) : Group (TBSBaer r G) where
  mul := (· * ·)
  mul_assoc := TBSBaer.mul_assoc_of_commutator_le_center hcomm
  one := 1
  one_mul := TBSBaer.one_mul
  mul_one := TBSBaer.mul_one
  inv := Inv.inv
  div := fun x y => x * y⁻¹
  div_eq_mul_inv := by intros; rfl
  zpow := zpowRec
  zpow_zero' := by intros; rfl
  zpow_succ' := by intros; rfl
  zpow_neg' := by intros; rfl
  inv_mul_cancel := TBSBaer.inv_mul_cancel

public def equiv {G : Type u} {r : ℕ} : TBSBaer r G ≃ G where
  toFun x := x.val
  invFun g := ⟨g⟩
  left_inv x := by cases x; rfl
  right_inv g := rfl

public instance finite {G : Type u} [Finite G] {r : ℕ} : Finite (TBSBaer r G) :=
  Finite.of_equiv G (equiv (G := G) (r := r)).symm

public theorem smul_commutatorElement
    {A G : Type u} [Group A] [Group G] [MulDistribMulAction A G]
    (a : A) (x y : G) :
    a • ⁅x, y⁆ = ⁅a • x, a • y⁆ := by
  simp [commutatorElement_def]

@[reducible]
public def action {A G : Type u} [Group A] [Group G] [MulDistribMulAction A G]
    {r : ℕ} (hcomm : _root_.commutator G ≤ Subgroup.center G) :
    letI : Group (TBSBaer r G) := group hcomm
    MulDistribMulAction A (TBSBaer r G) := by
  letI : Group (TBSBaer r G) := group hcomm
  exact {
    smul a x := ⟨a • x.val⟩
    one_smul x := by
      apply (ext_iff (G := G)).2
      change (1 : A) • x.val = x.val
      simp
    mul_smul a b x := by
      apply (ext_iff (G := G)).2
      change (a * b) • x.val = a • b • x.val
      simp [mul_smul]
    smul_mul a x y := by
      apply (ext_iff (G := G)).2
      change
        a • (x.val * y.val * ⁅y.val, x.val⁆ ^ r) =
          (a • x.val) * (a • y.val) * ⁅a • y.val, a • x.val⁆ ^ r
      simp [smul_commutatorElement]
    smul_one a := by
      apply (ext_iff (G := G)).2
      change a • (1 : G) = 1
      simp }

public theorem pow_two_mul_half_eq_self_of_pow_prime_eq_one
    {G : Type u} [Group G] {p r : ℕ}
    {c : G} (hc : c ^ p = 1) (hhalf : 2 * r = p + 1) :
    c ^ (2 * r) = c := by
  rw [hhalf, pow_succ, hc]
  simp

public theorem mul_comm
    {G : Type u} [Group G] {p r : ℕ}
    (hcomm : _root_.commutator G ≤ Subgroup.center G)
    (hpow : ∀ x : G, x ^ p = 1) (hhalf : 2 * r = p + 1)
    (x y : TBSBaer r G) :
    x * y = y * x := by
  apply (ext_iff (G := G)).2
  let c : G := ⁅y.val, x.val⁆
  have hc_cent : c ∈ Subgroup.center G :=
    commutator_mem_center_of_commutator_le_center hcomm y.val x.val
  have hc_pow : c ^ (2 * r) = c :=
    pow_two_mul_half_eq_self_of_pow_prime_eq_one (p := p) (r := r) (c := c) (hpow c) hhalf
  have hc_split : c = c ^ r * c ^ r := by
    simpa [pow_add, two_mul] using hc_pow.symm
  have hcomm_inv : ⁅x.val, y.val⁆ = c⁻¹ := by
    simp [c]
  have hcorr : c * c⁻¹ ^ r = c ^ r := by
    calc
      c * c⁻¹ ^ r = (c ^ r * c ^ r) * c⁻¹ ^ r := by
        exact congrArg (fun t : G => t * c⁻¹ ^ r) hc_split
      _ = c ^ r * (c ^ r * c⁻¹ ^ r) := by simp [mul_assoc]
      _ = c ^ r := by simp [inv_pow]
  calc
    ((x * y : TBSBaer r G) : G) = x.val * y.val * c ^ r := rfl
    _ = x.val * y.val * (c * c⁻¹ ^ r) := by
      rw [hcorr]
    _ = (x.val * y.val * c) * c⁻¹ ^ r := by simp [mul_assoc]
    _ = (y.val * x.val) * c⁻¹ ^ r := by
      rw [show y.val * x.val = x.val * y.val * c by
        simpa [c] using (TBSBaer.swap_mul_commutator_of_mem_center
          (x := x.val) (y := y.val) hc_cent)]
    _ = ((y * x : TBSBaer r G) : G) := by simp [hcomm_inv]

public theorem isMulCommutative
    {G : Type u} [Group G] {p r : ℕ}
    (hcomm : _root_.commutator G ≤ Subgroup.center G)
    (hpow : ∀ x : G, x ^ p = 1) (hhalf : 2 * r = p + 1) :
    letI : Group (TBSBaer r G) := group hcomm
    IsMulCommutative (TBSBaer r G) := by
  let : Group (TBSBaer r G) := group hcomm
  exact ⟨⟨fun x y => TBSBaer.mul_comm hcomm hpow hhalf x y⟩⟩

public theorem isPGroup
    {G : Type u} [Group G] [Finite G] {p r : ℕ} [Fact p.Prime]
    (hcomm : _root_.commutator G ≤ Subgroup.center G)
    (hG : IsPGroup p G) :
    letI : Group (TBSBaer r G) := group hcomm
    IsPGroup p (TBSBaer r G) := by
  let : Group (TBSBaer r G) := group hcomm
  obtain ⟨n, hcard⟩ := hG.exists_card_eq
  exact IsPGroup.of_card (p := p) (G := TBSBaer r G) (n := n) (by
    simpa [Nat.card_congr (equiv (G := G) (r := r))] using hcard)

end CFSG.TBSBaer

/--
Baer-additive endpoint for a minimal `Γ` member: the source's odd class-two
operator argument produces a nontrivial element in the Baer commutator subgroup
fixed by `A`; the centralizer hypothesis makes it fixed by `K`, contradicting
the coprime fixed/commutator decomposition in the Baer abelian group.
-/
public theorem CFSG.thompson_bender_minimal_gamma_baer_contradiction
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] (hpodd : p ≠ 2)
    {A K : Subgroup G}
    (hA_p : IsPGroup p A)
    (hcentral_order_p :
      ∀ x : G,
        x ∈ Subgroup.centralizer (A : Set G) → orderOf x = p → x ∈ A)
    (hA_norm_K : A ≤ Subgroup.normalizer (K : Set G))
    (hK_coprime : Nat.Coprime p (Nat.card K))
    {B : Subgroup (pCore p G)}
    (hB : TBSGammaMinimal (G := G) p A K B) :
    False := by
  classical
  let P : Subgroup G := pCore p G
  let r : ℕ := (p + 1) / 2
  have hhalf : 2 * r = p + 1 := by
    have hodd : Odd p := (Fact.out : Nat.Prime p).odd_of_ne_two hpodd
    rcases hodd with ⟨m, hm⟩
    subst p
    omega
  let hAleNormP : A ≤ Subgroup.normalizer (P : Set G) :=
    Subgroup.le_normalizer_of_normal (H := P)
  let φA : A →* MulAut P :=
    (Subgroup.normalizerMonoidHom (H := P)).comp (Subgroup.inclusion hAleNormP)
  let : MulDistribMulAction A P := MulDistribMulAction.compHom P φA
  have hBInvA : IsInvariant A P B := by
    simpa [P, φA, hAleNormP] using
      thompson_bender_minimal_gamma_A_conjAction_isInvariant
        (G := G) (p := p) (A := A) (K := K) (B := B) hB
  let : IsInvariant A P B := hBInvA
  let : MulDistribMulAction A B :=
    thompson_bender_subgroupMulDistribMulActionOfIsInvariant (A := A) (P := P) B
  let hKleNormP : K ≤ Subgroup.normalizer (P : Set G) :=
    Subgroup.le_normalizer_of_normal (H := P)
  let φK : K →* MulAut P :=
    (Subgroup.normalizerMonoidHom (H := P)).comp (Subgroup.inclusion hKleNormP)
  let : MulDistribMulAction K P := MulDistribMulAction.compHom P φK
  have hBInvK : IsInvariant K P B := by
    simpa [P, φK, hKleNormP] using
      thompson_bender_minimal_gamma_K_conjAction_isInvariant
        (G := G) (p := p) (A := A) (K := K) (B := B) hB
  let : IsInvariant K P B := hBInvK
  let : MulDistribMulAction K B :=
    thompson_bender_subgroupMulDistribMulActionOfIsInvariant (A := K) (P := P) B
  have hcommB : _root_.commutator B ≤ Subgroup.center B :=
    subgroup_commutator_le_center_of_commutator_le_centerIn (G := P) B
      (by
        simpa [P] using
          thompson_bender_minimal_gamma_commutator_le_centerIn
            (G := G) (p := p) (A := A) (K := K) (B := B) hB)
  let M : Type u := TBSBaer r B
  let : Group M := TBSBaer.group (G := B) (r := r) hcommB
  let : Finite M := TBSBaer.finite (G := B) (r := r)
  let : MulDistribMulAction A M := TBSBaer.action (A := A) (G := B) (r := r) hcommB
  let : MulDistribMulAction K M := TBSBaer.action (A := K) (G := B) (r := r) hcommB
  have hpowB : ∀ x : B, x ^ p = 1 := by
    have hdiv : Monoid.exponent B ∣ p := by
      simp [thompson_bender_minimal_gamma_exponent_eq
        (G := G) (p := p) (A := A) (K := K) (B := B) hB]
    exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hdiv
  have hMcomm : IsMulCommutative M := by
    simpa [M] using
      TBSBaer.isMulCommutative (G := B) (p := p) (r := r) hcommB hpowB hhalf
  let : IsMulCommutative M := hMcomm
  have hBp : IsPGroup p B := (pCore_isPGroup (G := G) (p := p)).to_subgroup B
  have hMp : IsPGroup p M := by
    simpa [M] using TBSBaer.isPGroup (G := B) (p := p) (r := r) hcommB hBp
  let C : Subgroup M := commutatorAction (A := K) (G := M)
  have hCp : IsPGroup p C := hMp.to_subgroup C
  have hCne : C ≠ ⊥ := by
    obtain ⟨k, x, hxB, hxnonfix⟩ :=
      thompson_bender_gamma_exists_nonfixed_action
        (G := G) (p := p) (A := A) (K := K) (X := B) hB.1
    let xb : B := ⟨x, hxB⟩
    let m : M := ⟨xb⟩
    have hmnonfix : k • m ≠ m := by
      intro hmfix
      apply hxnonfix
      change φK k x = x
      have hmf : ((k • m).val : P) = (m.val : P) :=
        congrArg (fun z : M => ((z.val : B) : P)) hmfix
      change φK k x = x at hmf
      exact hmf
    refine Subgroup.ne_bot_iff_exists_ne_one.mpr ?_
    have hgen : m⁻¹ * k • m ∈ C := by
      change m⁻¹ * k • m ∈ commutatorAction (A := K) (G := M)
      rw [commutatorAction_eq_closure]
      exact Subgroup.subset_closure ⟨k, m, rfl⟩
    refine ⟨⟨m⁻¹ * k • m, hgen⟩, ?_⟩
    intro hsubone
    have hval : m⁻¹ * k • m = (1 : M) := congrArg Subtype.val hsubone
    exact hmnonfix (inv_mul_eq_one.mp hval).symm
  have hCInvA : IsInvariant A M C := by
    have hforward : ∀ a : A, ∀ y : M, y ∈ C → a • y ∈ C := by
      intro a y hy
      change y ∈ commutatorAction (A := K) (G := M) at hy
      change a • y ∈ commutatorAction (A := K) (G := M)
      rw [commutatorAction_eq_closure] at hy ⊢
      let S : Set M := {z : M | ∃ k : K, ∃ g : M, z = g⁻¹ * k • g}
      change a • y ∈ Subgroup.closure S
      change y ∈ Subgroup.closure S at hy
      refine Subgroup.closure_induction
        (p := fun z _ => a • z ∈ Subgroup.closure S) ?_ ?_ ?_ ?_ hy
      · intro z hz
        rcases hz with ⟨k, g, rfl⟩
        let k' : K := thompson_bender_conjKOfANormalizes (G := G) hA_norm_K a k
        have hcomp : a • (k • g) = k' • (a • g) := by
          apply (TBSBaer.ext_iff (G := B)).2
          apply Subtype.ext
          change φA a (φK k ((g.val : B) : P)) =
            φK k' (φA a ((g.val : B) : P))
          simpa [P, φA, φK, hAleNormP, hKleNormP, k'] using
            thompson_bender_pCore_conjAction_A_comp_K_eq_conjK
              (G := G) (p := p) (A := A) (K := K) hA_norm_K a k ((g.val : B) : P)
        have hgen :
            a • (g⁻¹ * k • g) = (a • g)⁻¹ * k' • (a • g) := by
          simp [hcomp]
        exact Subgroup.subset_closure ⟨k', a • g, hgen⟩
      · simp
      · intro x y _ _ hx hy
        simpa using (Subgroup.mul_mem (Subgroup.closure S) hx hy)
      · intro x _ hx
        simpa using (Subgroup.inv_mem (Subgroup.closure S) hx)
    refine ⟨?_⟩
    intro a y
    constructor
    · exact hforward a y
    · intro hy
      have hpre : a⁻¹ • (a • y) ∈ C := hforward a⁻¹ (a • y) hy
      simpa using hpre
  let : IsInvariant A M C := hCInvA
  have hInfNe : C ⊓ fixedPointSubgroup A M ≠ ⊥ :=
    thompson_bender_inf_fixedPointSubgroup_ne_bot_of_pgroup_action
      (P := M) (A := A) (p := p) (B := C) hCp hA_p hCne
  rcases Subgroup.ne_bot_iff_exists_ne_one.mp hInfNe with ⟨m0, hm0ne⟩
  let m : M := m0
  have hmComm : m ∈ C := m0.property.1
  have hmFixA : m ∈ fixedPointSubgroup A M := m0.property.2
  have hmne : m ≠ 1 := by
    intro hm
    exact hm0ne (Subtype.ext hm)
  let u : P := (m.val : B)
  have huB : u ∈ B := (m.val : B).property
  have hune : u ≠ 1 := by
    intro hu
    apply hmne
    apply (TBSBaer.ext_iff (G := B)).2
    exact Subtype.ext hu
  have huFixA : u ∈ fixedPointSubgroup A P := by
    rw [FixedPoints.mem_subgroup]
    intro a
    have hma : a • m = m :=
      (FixedPoints.mem_subgroup (M := A) (α := M) (a := m)).1 hmFixA a
    have hmaP : ((TBSBaer.val (a • m) : B) : P) = ((TBSBaer.val m : B) : P) :=
      congrArg (fun z : M => ((TBSBaer.val z : B) : P)) hma
    change ((TBSBaer.val (a • m) : B) : P) = ((TBSBaer.val m : B) : P)
    exact hmaP
  have huCentA : (u : G) ∈ Subgroup.centralizer (A : Set G) := by
    exact
      (thompson_bender_pCore_mem_centralizer_iff_mem_fixedPointSubgroup
        (G := G) (p := p) (L := A) (x := u)).mpr (by simpa [P] using huFixA)
  have huFixedK : ∀ k : K, φK k u = u := by
    simpa [P, φK, hKleNormP] using
      thompson_bender_minimal_gamma_mem_centralizer_A_fixed_by_conjAction
        (G := G) (p := p) (A := A) (K := K) (B := B)
        hcentral_order_p hA_norm_K hK_coprime hB huB hune huCentA
  have hmFixK : m ∈ fixedPointSubgroup K M := by
    rw [FixedPoints.mem_subgroup]
    intro k
    apply (TBSBaer.ext_iff (G := B)).2
    apply Subtype.ext
    change φK k u = u
    exact huFixedK k
  have hcopKB : Nat.Coprime (Nat.card K) (Nat.card B) := by
    obtain ⟨n, hBcard⟩ := hBp.exists_card_eq
    rw [hBcard]
    exact hK_coprime.symm.pow_right n
  have hcopKM : Nat.Coprime (Nat.card K) (Nat.card M) := by
    have hcardM : Nat.card M = Nat.card B := by
      simpa [M] using Nat.card_congr (TBSBaer.equiv (G := B) (r := r))
    rw [hcardM]
    exact hcopKB
  have hsolvM : Group.IsSolvable M := by infer_instance
  have hbot : fixedPointSubgroup K M ⊓ C = ⊥ := by
    simpa [C] using
      thompson_bender_fixedPointSubgroup_inf_commutatorAction_eq_bot_of_solvable_coprime_comm
        (P := M) (A := K) hsolvM hcopKM hMcomm
  have hmBot : m ∈ (⊥ : Subgroup M) := by
    simpa [hbot] using (show m ∈ fixedPointSubgroup K M ⊓ C from ⟨hmFixK, hmComm⟩)
  exact hmne (Subgroup.mem_bot.mp hmBot)

/--
For a minimal `Γ` member, the all-`K` displacement subgroup has a nontrivial
point fixed by the induced `A` action.
-/
public theorem CFSG.thompson_bender_minimal_gamma_all_displacement_inf_fixedPoint_ne_bot
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {A K : Subgroup G} {B : Subgroup (pCore p G)}
    (hA_p : IsPGroup p A)
    (hA_norm_K : A ≤ Subgroup.normalizer (K : Set G))
    (hB : TBSGammaMinimal (G := G) p A K B) :
    let P : Subgroup G := pCore p G
    let hAleNormP : A ≤ Subgroup.normalizer (P : Set G) :=
      Subgroup.le_normalizer_of_normal (H := P)
    let φA : A →* MulAut P :=
      (Subgroup.normalizerMonoidHom (H := P)).comp (Subgroup.inclusion hAleNormP)
    letI : MulDistribMulAction A P := MulDistribMulAction.compHom P φA
    TBSConjActionDisplacementSubgroupAll (G := G) p K B ⊓
      fixedPointSubgroup A P ≠ ⊥ := by
  let P : Subgroup G := pCore p G
  let hAleNormP : A ≤ Subgroup.normalizer (P : Set G) :=
    Subgroup.le_normalizer_of_normal (H := P)
  let φA : A →* MulAut P :=
    (Subgroup.normalizerMonoidHom (H := P)).comp (Subgroup.inclusion hAleNormP)
  let : MulDistribMulAction A P := MulDistribMulAction.compHom P φA
  change
    TBSConjActionDisplacementSubgroupAll (G := G) p K B ⊓
      fixedPointSubgroup A P ≠ ⊥
  have hBInv :
      IsInvariant A P B := by
    simpa [P, φA, hAleNormP] using
      thompson_bender_minimal_gamma_A_conjAction_isInvariant
        (G := G) (p := p) (A := A) (K := K) (B := B) hB
  have hAllInv :
      IsInvariant A P (TBSConjActionDisplacementSubgroupAll (G := G) p K B) := by
    simpa [P, φA, hAleNormP] using
      thompson_bender_conjAction_displacementSubgroupAll_A_isInvariant
        (G := G) (p := p) (A := A) (K := K) (B := B)
        hA_norm_K (by simpa [P, φA, hAleNormP] using hBInv)
  let : IsInvariant A P (TBSConjActionDisplacementSubgroupAll (G := G) p K B) := hAllInv
  obtain ⟨k, x, hxB, hxnonfix⟩ :=
    thompson_bender_gamma_exists_nonfixed_action
      (G := G) (p := p) (A := A) (K := K) (X := B) hB.1
  let hKleNormP : K ≤ Subgroup.normalizer (P : Set G) :=
    Subgroup.le_normalizer_of_normal (H := P)
  let φK : K →* MulAut P :=
    (Subgroup.normalizerMonoidHom (H := P)).comp (Subgroup.inclusion hKleNormP)
  have hAllNe :
      TBSConjActionDisplacementSubgroupAll (G := G) p K B ≠ ⊥ := by
    simpa [P, φK, hKleNormP] using
      thompson_bender_conjAction_displacementSubgroupAll_ne_bot_of_nonfixed
        (G := G) (p := p) (K := K) (B := B) k x hxB hxnonfix
  exact
    thompson_bender_inf_fixedPointSubgroup_ne_bot_of_pgroup_action
      (P := P) (A := A) (p := p)
      (B := TBSConjActionDisplacementSubgroupAll (G := G) p K B)
      (thompson_bender_conjAction_displacementSubgroupAll_isPGroup
        (G := G) (p := p) (K := K) (B := B))
      hA_p hAllNe

/--
Element form of the preceding fixed-point step: a minimal `Γ` member contains
a nontrivial all-displacement element centralizing `A`.
-/
public theorem CFSG.thompson_bender_minimal_gamma_exists_nontrivial_all_displacement_centralizer_A
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {A K : Subgroup G} {B : Subgroup (pCore p G)}
    (hA_p : IsPGroup p A)
    (hA_norm_K : A ≤ Subgroup.normalizer (K : Set G))
    (hB : TBSGammaMinimal (G := G) p A K B) :
    ∃ u : pCore p G,
      u ∈ B ∧
        u ∈ TBSConjActionDisplacementSubgroupAll (G := G) p K B ∧
          u ≠ 1 ∧ (u : G) ∈ Subgroup.centralizer (A : Set G) := by
  let P : Subgroup G := pCore p G
  let hAleNormP : A ≤ Subgroup.normalizer (P : Set G) :=
    Subgroup.le_normalizer_of_normal (H := P)
  let φA : A →* MulAut P :=
    (Subgroup.normalizerMonoidHom (H := P)).comp (Subgroup.inclusion hAleNormP)
  let : MulDistribMulAction A P := MulDistribMulAction.compHom P φA
  have hNontr :
      TBSConjActionDisplacementSubgroupAll (G := G) p K B ⊓
        fixedPointSubgroup A P ≠ ⊥ := by
    simpa [P, φA, hAleNormP] using
      thompson_bender_minimal_gamma_all_displacement_inf_fixedPoint_ne_bot
        (G := G) (p := p) (A := A) (K := K) (B := B)
        hA_p hA_norm_K hB
  obtain ⟨u, huAll, hune, huCentA⟩ :=
    thompson_bender_pCore_exists_nontrivial_mem_centralizer_of_inf_fixedPointSubgroup_ne_bot
      (G := G) (p := p) (L := A)
      (B := TBSConjActionDisplacementSubgroupAll (G := G) p K B) hNontr
  exact ⟨u,
    thompson_bender_minimal_gamma_displacementSubgroupAll_le
      (G := G) (p := p) (A := A) (K := K) (B := B) hB huAll,
    huAll, hune, huCentA⟩

/-- The ambient image of a minimal `Γ` member is not centralized by `K`. -/
public theorem CFSG.thompson_bender_minimal_gamma_not_le_centralizer
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} {A K : Subgroup G} {B : Subgroup (pCore p G)}
    (hB : TBSGammaMinimal (G := G) p A K B) :
    ¬ B.map (pCore p G).subtype ≤ Subgroup.centralizer (K : Set G) := by
  rcases hB.1 with ⟨D, hD⟩
  rcases hD with ⟨hDB, hDchar, hDcomm, hDclass, hDexp, hnorm, hnot⟩
  have hEq : D = B := by
    exact thompson_bender_minimal_gamma_eq_witness
      (G := G) (p := p) (A := A) (K := K)
      (B := B) (D := D) hB
      ⟨hDB, hDchar, hDcomm, hDclass, hDexp, hnorm, hnot⟩
  subst B
  simpa using hnot

/-- For a minimal `Γ` member, the conjugation image of `K` does not fix `B` pointwise. -/
public theorem CFSG.thompson_bender_minimal_gamma_not_action_range_le_fixing
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} {A K : Subgroup G} {B : Subgroup (pCore p G)}
    (hB : TBSGammaMinimal (G := G) p A K B) :
    ¬
      (let P : Subgroup G := pCore p G
       let hKleNormP : K ≤ Subgroup.normalizer (P : Set G) :=
          Subgroup.le_normalizer_of_normal (H := P)
       let φ : K →* MulAut P :=
          (Subgroup.normalizerMonoidHom (H := P)).comp (Subgroup.inclusion hKleNormP)
       φ.range ≤ fixingSubgroup (M := MulAut P) (α := P) (B : Set P)) := by
  intro hfix
  exact
    thompson_bender_minimal_gamma_not_le_centralizer
      (G := G) (p := p) (A := A) (K := K) (B := B) hB
      ((thompson_bender_pCore_subgroup_map_le_centralizer_iff
        (G := G) (p := p) (D := B) (K := K)).2
        (thompson_bender_subtype_le_centralizer_of_action_range_le_fixing
          (G := G) (P := pCore p G) (K := K) (D := B) (by
            simpa using hfix)))

/-- A nonempty `Γ` has a cardinal-minimal member. -/
public theorem CFSG.thompson_bender_exists_minimal_gamma_of_nonempty
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} {A K : Subgroup G}
    (hne : ∃ X : Subgroup (pCore p G), TBSGamma (G := G) p A K X) :
    ∃ B : Subgroup (pCore p G), TBSGammaMinimal (G := G) p A K B := by
  classical
  let HasCard : ℕ → Prop := fun n =>
    ∃ X : Subgroup (pCore p G), TBSGamma (G := G) p A K X ∧ Nat.card X = n
  have hHasCard : ∃ n : ℕ, HasCard n := by
    rcases hne with ⟨X, hX⟩
    exact ⟨Nat.card X, X, hX, rfl⟩
  let n0 : ℕ := Nat.find hHasCard
  rcases Nat.find_spec hHasCard with ⟨B, hB, hBcard⟩
  refine ⟨B, ?_⟩
  refine ⟨hB, ?_⟩
  intro X hX
  have hXcard : HasCard (Nat.card X) := ⟨X, hX, rfl⟩
  have hmin : n0 ≤ Nat.card X := Nat.find_min' hHasCard hXcard
  rw [hBcard]
  exact hmin

/-- Unpacked critical-subgroup witness inside `O_p(G)`. -/
public theorem CFSG.thompson_bender_pCore_criticalSubgroup_witness
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] (hpodd : p ≠ 2)
    (hPne : pCore p G ≠ ⊥) :
    ∃ D : Subgroup (pCore p G),
      D.Characteristic ∧
        (⁅D, ⊤⁆ ≤ centerIn (G := pCore p G) D) ∧
        NilpotencyClassLe 2 (↥D) ∧
        (Monoid.exponent (↥D) = p) ∧
        IsPGroup p
          (↥(fixingSubgroup (M := MulAut (pCore p G)) (α := pCore p G)
            (D : Set (pCore p G)))) := by
  let P : Subgroup G := pCore p G
  let : Fact (IsPGroup p P) := ⟨pCore_isPGroup (G := G) (p := p)⟩
  let : Nontrivial P := P.nontrivial_iff_ne_bot.mpr (by simpa [P] using hPne)
  simpa [P] using theorem_1_13 (G := P) (p := p) hpodd

/-- If `O_p(G)` is trivial, every subgroup centralizes it. -/
public theorem CFSG.thompson_bender_le_centralizer_pCore_of_pCore_eq_bot
    {G : Type u} [Group G] {p : ℕ} {K : Subgroup G}
    (hPbot : pCore p G = ⊥) :
    K ≤ Subgroup.centralizer (pCore p G : Set G) := by
  intro k hk
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have hyone : y = 1 := by
    have : y ∈ (⊥ : Subgroup G) := by simpa [hPbot] using hy
    simpa using this
  simp [hyone]

/--
Critical-subgroup endpoint: if every Theorem 1.13 critical witness inside
`O_p(G)` centralizes `K`, then the `p'` subgroup `K` centralizes `O_p(G)`.
-/
public theorem CFSG.thompson_bender_le_centralizer_pCore_of_critical_witnesses_centralize
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] (hpodd : p ≠ 2)
    {K : Subgroup G}
    (hK_coprime : Nat.Coprime p (Nat.card K))
    (hCritCent :
      ∀ D : Subgroup (pCore p G),
        D.Characteristic →
          (⁅D, ⊤⁆ ≤ centerIn (G := pCore p G) D) →
            NilpotencyClassLe 2 (↥D) →
              Monoid.exponent (↥D) = p →
                ∀ x : pCore p G, x ∈ D →
                  (x : G) ∈ Subgroup.centralizer (K : Set G)) :
    K ≤ Subgroup.centralizer (pCore p G : Set G) := by
  classical
  by_cases hPbot : pCore p G = ⊥
  · exact thompson_bender_le_centralizer_pCore_of_pCore_eq_bot
      (G := G) (p := p) (K := K) hPbot
  · obtain ⟨D, hDchar, hDcomm, hDclass, hDexp, hDfixp⟩ :=
      thompson_bender_pCore_criticalSubgroup_witness
        (G := G) (p := p) hpodd hPbot
    exact
      thompson_bender_le_centralizer_of_coprime_action_range_le_fixing
        (G := G) (p := p) (P := pCore p G) (K := K) (D := D)
        hK_coprime hDfixp
        (thompson_bender_action_range_le_fixing_of_subtype_le_centralizer
          (G := G) (P := pCore p G) (K := K) (D := D)
          (hCritCent D hDchar hDcomm hDclass hDexp))

/--
Source-hard critical-witness core for the reduced Thompson--Bender argument.
In the reduced quotient, every Theorem 1.13 critical witness inside `O_p(G)`
must centralize the `p'` signalizer subgroup.
-/
public theorem CFSG.thompson_bender_reduced_critical_witness_centralizes_K
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] (hpodd : p ≠ 2)
    (_hcore_bot : pPrimeCore p G = ⊥)
    (_hconstr : Subgroup.centralizer (pCore p G : Set G) ≤ pCore p G)
    {A K : Subgroup G}
    (hA_p : IsPGroup p A)
    (hcentral_order_p :
      ∀ x : G,
        x ∈ Subgroup.centralizer (A : Set G) → orderOf x = p → x ∈ A)
    (hA_le_normalizer_K : A ≤ Subgroup.normalizer (K : Set G))
    (_hK_inf_A : K ⊓ A = ⊥)
    (hK_coprime : Nat.Coprime p (Nat.card K))
    {D : Subgroup (pCore p G)}
    (hDchar : D.Characteristic)
    (hDcomm : ⁅D, ⊤⁆ ≤ centerIn (G := pCore p G) D)
    (hDclass : NilpotencyClassLe 2 (↥D))
    (hDexp : Monoid.exponent (↥D) = p) :
    ∀ x : pCore p G, x ∈ D → (x : G) ∈ Subgroup.centralizer (K : Set G) := by
  classical
  by_cases hPbot : pCore p G = ⊥
  · intro x _hxD
    have hxone : (x : G) = 1 := by
      have hxbot : (x : G) ∈ (⊥ : Subgroup G) := by
        simpa [hPbot] using x.property
      simpa using hxbot
    simp [hxone]
  · by_contra hnotPoint
    have hnotMap :
        ¬ D.map (pCore p G).subtype ≤ Subgroup.centralizer (K : Set G) := by
      intro hle
      exact hnotPoint
        ((thompson_bender_pCore_subgroup_map_le_centralizer_iff
          (G := G) (p := p) (D := D) (K := K)).1 hle)
    have hnorm :
        A ⊔ K ≤ Subgroup.normalizer
          (((D.map (pCore p G).subtype : Subgroup G) : Set G)) := by
      exact
        thompson_bender_le_normalizer_pCore_characteristic_subgroup
          (G := G) (p := p) (D := D) hDchar (A ⊔ K)
    have htop : TBSGamma (G := G) p A K ⊤ :=
      thompson_bender_gamma_top_of_critical_witness
        (G := G) (p := p) (A := A) (K := K) (D := D)
        hDchar hDcomm hDclass hDexp hnorm hnotMap
    obtain ⟨B, hB⟩ :=
      thompson_bender_exists_minimal_gamma_of_nonempty
        (G := G) (p := p) (A := A) (K := K) ⟨⊤, htop⟩
    have hminimal_contra :
        ∀ B : Subgroup (pCore p G),
          TBSGammaMinimal (G := G) p A K B → False := by
      intro B hB
      exact
        thompson_bender_minimal_gamma_baer_contradiction
          (G := G) (p := p) (A := A) (K := K) (B := B)
          hpodd hA_p hcentral_order_p hA_le_normalizer_K hK_coprime hB
    exact False.elim (hminimal_contra B hB)

/--
The reduced Thompson--Bender core: once the signalizer subgroup is known to be
`p'`, the signalizer subgroup centralizes the quotient `p`-core.
-/
public theorem CFSG.thompson_bender_map_le_centralizer_pCore_quotient_of_coprime_signalizer
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] (hpodd : p ≠ 2)
    (hconstrained : PConstrainedGroup (G := G) p)
    {A K : Subgroup G}
    (hA_p : IsPGroup p A)
    (hcentral_order_p :
      ∀ x : G,
        x ∈ Subgroup.centralizer (A : Set G) → orderOf x = p → x ∈ A)
    (hA_le_normalizer_K : A ≤ Subgroup.normalizer (K : Set G))
    (_hK_inf_A : K ⊓ A = ⊥)
    (hK_coprime : Nat.Coprime p (Nat.card K)) :
    let q : G →* G ⧸ pPrimeCore p G := QuotientGroup.mk' (pPrimeCore p G)
    K.map q ≤
      Subgroup.centralizer
        (pCore p (G ⧸ pPrimeCore p G) : Set (G ⧸ pPrimeCore p G)) := by
  classical
  let q : G →* G ⧸ pPrimeCore p G := QuotientGroup.mk' (pPrimeCore p G)
  let Aq : Subgroup (G ⧸ pPrimeCore p G) := A.map q
  let Kq : Subgroup (G ⧸ pPrimeCore p G) := K.map q
  have hKq_coprime : Nat.Coprime p (Nat.card Kq) := by
    simpa [Kq, q] using
      thompson_bender_quotient_signalizer_coprime_card
        (G := G) (p := p) (K := K) hK_coprime
  have hAq_p : IsPGroup p Aq := by
    simpa [Aq, q] using
      thompson_bender_quotient_A_isPGroup (G := G) (p := p) (A := A) hA_p
  have hcentral_q :
      ∀ x : G ⧸ pPrimeCore p G,
        x ∈ Subgroup.centralizer (Aq : Set (G ⧸ pPrimeCore p G)) → orderOf x = p → x ∈ Aq := by
    intro x hxcentral hxorder
    simpa [Aq, q] using
      thompson_bender_quotient_centralizer_order_p
        (G := G) (p := p) (A := A) hA_p hcentral_order_p
        (x := x) (by simpa [Aq, q] using hxcentral) hxorder
  have hAq_norm_Kq : Aq ≤ Subgroup.normalizer (Kq : Set (G ⧸ pPrimeCore p G)) := by
    simpa [Aq, Kq, q] using
      thompson_bender_quotient_A_le_normalizer_K
        (G := G) (p := p) (A := A) (K := K) hA_le_normalizer_K
  have hKq_inf_Aq : Kq ⊓ Aq = ⊥ := by
    simpa [Kq, Aq, q] using
      thompson_bender_quotient_K_inf_A_eq_bot
        (G := G) (p := p) (A := A) (K := K) hA_p hK_coprime
  have hquot_core_bot : pPrimeCore p (G ⧸ pPrimeCore p G) = ⊥ := by
    simpa [q] using pPrimeCore_quotient_pPrimeCore_eq_bot (G := G) (p := p)
  have hquot_constr :
      Subgroup.centralizer (pCore p (G ⧸ pPrimeCore p G) : Set (G ⧸ pPrimeCore p G)) ≤
        pCore p (G ⧸ pPrimeCore p G) :=
    thompson_bender_centralizer_pCore_quotient_le_pCore
      (G := G) (p := p) hconstrained
  exact
    thompson_bender_le_centralizer_pCore_of_critical_witnesses_centralize
      (G := G ⧸ pPrimeCore p G) (p := p) hpodd (K := Kq) hKq_coprime
      (by
        intro D hDchar hDcomm hDclass hDexp x hxD
        exact
          thompson_bender_reduced_critical_witness_centralizes_K
            (G := G ⧸ pPrimeCore p G) (p := p) hpodd
            hquot_core_bot hquot_constr
            (A := Aq) (K := Kq)
            hAq_p hcentral_q hAq_norm_Kq hKq_inf_Aq hKq_coprime
            hDchar hDcomm hDclass hDexp x hxD)

/--
The reduced Thompson--Bender endpoint: once the signalizer subgroup is known to
be `p'`, the p-constrained hypothesis forces it into `O_{p',p}(G)`.
-/
public theorem CFSG.thompson_bender_le_Op_p'p_of_coprime_signalizer
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] (hpodd : p ≠ 2)
    (hconstrained : PConstrainedGroup (G := G) p)
    {A K : Subgroup G}
    (hA_p : IsPGroup p A)
    (hcentral_order_p :
      ∀ x : G,
        x ∈ Subgroup.centralizer (A : Set G) → orderOf x = p → x ∈ A)
    (hA_le_normalizer_K : A ≤ Subgroup.normalizer (K : Set G))
    (hK_inf_A : K ⊓ A = ⊥)
    (hK_coprime : Nat.Coprime p (Nat.card K)) :
    K ≤ Op_p'p p G := by
  exact
    thompson_bender_le_Op_p'p_of_map_le_centralizer_pCore_quotient
      (G := G) (p := p) hconstrained
      (thompson_bender_map_le_centralizer_pCore_quotient_of_coprime_signalizer
        (G := G) (p := p) hpodd hconstrained hA_p hcentral_order_p
        hA_le_normalizer_K hK_inf_A hK_coprime)

/--
Huppert--Blackburn X.1.12, Thompson--Bender.

The proof is intentionally left as the single core placeholder corresponding to
the step-proof route.  No theorem-to-prove wrapper hypothesis is introduced.
-/
public theorem CFSG.thompson_bender_signalizer_lemma
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] (hpodd : p ≠ 2)
    (hconstrained : PConstrainedGroup (G := G) p)
    {A K : Subgroup G}
    (hA_p : IsPGroup p A)
    (hcentral_order_p :
      ∀ x : G,
        x ∈ Subgroup.centralizer (A : Set G) → orderOf x = p → x ∈ A)
    (hA_le_normalizer_K : A ≤ Subgroup.normalizer (K : Set G))
    (hK_inf_A : K ⊓ A = ⊥) :
    K ≤ pPrimeCore p G := by
  have hK_coprime : Nat.Coprime p (Nat.card K) :=
    thompson_bender_coprime_card_of_centralizer_order_p
      (G := G) (p := p) hA_p hcentral_order_p hA_le_normalizer_K hK_inf_A
  have hK_le_Op : K ≤ Op_p'p p G :=
    thompson_bender_le_Op_p'p_of_coprime_signalizer
      (G := G) (p := p) hpodd hconstrained hA_p hcentral_order_p
      hA_le_normalizer_K hK_inf_A hK_coprime
  exact thompson_bender_le_pPrimeCore_of_le_Op_p'p hK_le_Op hK_coprime

/-- Pointwise application form of `thompson_bender_signalizer_lemma`. -/
public theorem CFSG.thompson_bender_signalizer_lemma_apply
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] (hpodd : p ≠ 2)
    (hconstrained : PConstrainedGroup (G := G) p)
    {A K : Subgroup G}
    (hA_p : IsPGroup p A)
    (hcentral_order_p :
      ∀ x : G,
        x ∈ Subgroup.centralizer (A : Set G) → orderOf x = p → x ∈ A)
    (hA_le_normalizer_K : A ≤ Subgroup.normalizer (K : Set G))
    (hK_inf_A : K ⊓ A = ⊥)
    {x : G} (hx : x ∈ K) :
    x ∈ pPrimeCore p G :=
  thompson_bender_signalizer_lemma
    (G := G) (p := p) hpodd hconstrained hA_p hcentral_order_p
    hA_le_normalizer_K hK_inf_A hx
