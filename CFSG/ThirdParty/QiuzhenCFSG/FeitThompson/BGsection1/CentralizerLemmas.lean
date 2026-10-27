module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.Defs
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Fitting.Centralizer

namespace CFSG
end CFSG
open CFSG

open scoped Pointwise commutatorElement

public lemma CFSG.centralizer_le_normalizer {G : Type*} [Group G] (R : Subgroup G) :
    Subgroup.centralizer (R : Set G) ≤ Subgroup.normalizer R := by
  intro x hxC
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    have hxy : y * x = x * y := (Subgroup.mem_centralizer_iff.mp hxC) y hy
    have hconj : x * y * x⁻¹ = y := by
      calc
        x * y * x⁻¹ = (x * y) * x⁻¹ := by simp [mul_assoc]
        _ = (y * x) * x⁻¹ := by rw [hxy.symm]
        _ = y := by simp [mul_assoc]
    simpa [hconj] using hy
  · intro hy
    have hxinvC : x⁻¹ ∈ Subgroup.centralizer (R : Set G) :=
      (Subgroup.inv_mem_iff (H := Subgroup.centralizer (R : Set G))).2 hxC
    have hy' : x⁻¹ * (x * y * x⁻¹) * x ∈ R := by
      have hyc : x * y * x⁻¹ ∈ R := hy
      have hxy : (x * y * x⁻¹) * x⁻¹ = x⁻¹ * (x * y * x⁻¹) :=
        (Subgroup.mem_centralizer_iff.mp hxinvC) (x * y * x⁻¹) hyc
      have hconj : x⁻¹ * (x * y * x⁻¹) * x = x * y * x⁻¹ := by
        calc
          x⁻¹ * (x * y * x⁻¹) * x = (x⁻¹ * (x * y * x⁻¹)) * x := by simp [mul_assoc]
          _ = ((x * y * x⁻¹) * x⁻¹) * x := by rw [hxy]
          _ = x * y * x⁻¹ := by simp [mul_assoc]
      simpa [hconj] using hyc
    simpa [mul_assoc] using hy'

public lemma CFSG.centralizer_subgroupOf_normalizer_eq {G : Type*} [Group G] (R : Subgroup G) :
    Subgroup.centralizer ((R.subgroupOf (Subgroup.normalizer R)) : Set (Subgroup.normalizer (R : Set G))) =
      (Subgroup.centralizer (R : Set G)).subgroupOf (Subgroup.normalizer (R : Set G)) := by
  let N : Subgroup G := Subgroup.normalizer R
  ext x
  constructor
  · intro hx
    change (x : G) ∈ Subgroup.centralizer (R : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    let yN : N := ⟨y, (Subgroup.le_normalizer (H := R)) hy⟩
    have hyN : yN ∈ R.subgroupOf N := hy
    have hcomm := (Subgroup.mem_centralizer_iff.mp hx) yN hyN
    exact congrArg Subtype.val hcomm
  · intro hx
    change (x : G) ∈ Subgroup.centralizer (R : Set G) at hx
    rw [Subgroup.mem_centralizer_iff] at hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    apply Subtype.ext
    exact hx (y : G) hy

public theorem Subgroup.le_centralizer_sup_of_le_centralizers
    {G : Type*} [Group G] {R A B : Subgroup G}
    (hRA : R ≤ Subgroup.centralizer (A : Set G))
    (hRB : R ≤ Subgroup.centralizer (B : Set G)) :
    R ≤ Subgroup.centralizer ((A ⊔ B : Subgroup G) : Set G) := by
  intro r hr
  rw [Subgroup.sup_eq_closure, Subgroup.centralizer_closure, Subgroup.mem_centralizer_iff]
  intro x hx
  rcases hx with hxA | hxB
  · exact Subgroup.mem_centralizer_iff.mp (hRA hr) x hxA
  · exact Subgroup.mem_centralizer_iff.mp (hRB hr) x hxB

public theorem Subgroup.le_normalizer_inf
    {G : Type*} [Group G] {A H K : Subgroup G}
    (hAH : A ≤ Subgroup.normalizer (H : Set G))
    (hAK : A ≤ Subgroup.normalizer (K : Set G)) :
    A ≤ Subgroup.normalizer (H ⊓ K : Set G) := by
  intro a ha
  exact Subgroup.inf_normalizer_le_normalizer_inf ⟨hAH ha, hAK ha⟩

public lemma CFSG.pPrimeCore_le_centralizer_of_normal_pgroup {G : Type*} [Group G] [Finite G]
    (p : ℕ) [Fact p.Prime] (R : Subgroup G) [R.Normal] (hRp : IsPGroup p (↥R)) :
    pPrimeCore p G ≤ Subgroup.centralizer (R : Set G) := by
  intro x hx
  rw [Subgroup.mem_centralizer_iff_commutator_eq_one]
  intro r hr
  have hcomm : ⁅r, x⁆ ∈ ⁅R, pPrimeCore p G⁆ :=
    Subgroup.commutator_mem_commutator hr hx
  have hle : ⁅R, pPrimeCore p G⁆ ≤ R ⊓ pPrimeCore p G :=
    Subgroup.commutator_le_inf (H₁ := R) (H₂ := pPrimeCore p G)
  have hcomm_inf : ⁅r, x⁆ ∈ R ⊓ pPrimeCore p G := hle hcomm
  have hcopR : Nat.Coprime (Nat.card R) (Nat.card (pPrimeCore p G)) := by
    rcases hRp.exists_card_eq with ⟨n, hn⟩
    rw [hn]
    exact (pPrimeCore_coprime_card (G := G) (p := p)).pow_left n
  have hinf_bot : R ⊓ pPrimeCore p G = ⊥ :=
    disjoint_iff.mp (Subgroup.disjoint_of_coprime_natCard hcopR)
  have hcomm_bot : ⁅r, x⁆ ∈ (⊥ : Subgroup G) := by
    simpa [hinf_bot] using hcomm_inf
  simpa using hcomm_bot

public theorem CFSG.le_pPrimeCore_of_le_Op_p'p_of_coprime {G : Type*} [Group G] (p : ℕ) [Fact p.Prime]
    {H : Subgroup G} (hHle : H ≤ Op_p'p p G) (hcop : Nat.Coprime p (Nat.card H)) :
    H ≤ pPrimeCore p G := by
  let M : Subgroup G := pPrimeCore p G
  let q : G →* G ⧸ M := QuotientGroup.mk' M
  have hmap_op : (Op_p'p p G).map q = pCore p (G ⧸ M) := by
    dsimp [Op_p'p, q, M]
    simpa using
      (Subgroup.map_comap_eq_self_of_surjective
        (f := QuotientGroup.mk' (pPrimeCore p G))
        (h := QuotientGroup.mk'_surjective (pPrimeCore p G))
        (H := pCore p (G ⧸ pPrimeCore p G)))
  have hHmap_le : H.map q ≤ pCore p (G ⧸ M) :=
    (Subgroup.map_mono hHle).trans hmap_op.le
  have hHmap_p : IsPGroup p (H.map q) :=
    IsPGroup.to_le (hK := pCore_isPGroup (p := p) (G := (G ⧸ M))) hHmap_le
  have hHmap_coprime : Nat.Coprime p (Nat.card (H.map q)) := by
    exact Nat.Coprime.of_dvd_right (Subgroup.card_map_dvd (H := H) q) hcop
  have hHmap_card_eq_one : Nat.card (H.map q) = 1 := by
    rcases hHmap_p.card_eq_or_dvd with h1 | hpdvd
    · exact h1
    · exfalso
      exact ((Nat.Prime.coprime_iff_not_dvd (Fact.out : Nat.Prime p)).1 hHmap_coprime) hpdvd
  have hHmap_bot : H.map q = ⊥ := Subgroup.card_eq_one.mp hHmap_card_eq_one
  have hHle_ker : H ≤ q.ker := by
    intro x hx
    have hxmap : q x ∈ H.map q := Subgroup.mem_map_of_mem q hx
    have hx1 : q x = 1 := by
      have hxbot : q x ∈ (⊥ : Subgroup (G ⧸ M)) := by simpa [hHmap_bot] using hxmap
      simpa using hxbot
    simpa [MonoidHom.mem_ker] using hx1
  simpa [q, M] using hHle_ker

public theorem CFSG.pPrimeCore_quotient_pPrimeCore_eq_bot {G : Type*} [Group G] [Finite G]
    (p : ℕ) [Fact p.Prime] :
    pPrimeCore p (G ⧸ pPrimeCore p G) = ⊥ := by
  let M : Subgroup G := pPrimeCore p G
  let q : G →* G ⧸ M := QuotientGroup.mk' M
  have hqsurj : Function.Surjective q := QuotientGroup.mk'_surjective M
  have hMcop : Nat.Coprime p (Nat.card M) := by
    simpa [M] using (pPrimeCore_coprime_card (G := G) (p := p))
  refine (pPrimeCore_eq_bot_iff (p := p) (G := (G ⧸ M))).2 ?_
  intro K hKnorm hKcop
  let N : Subgroup G := K.comap q
  have hNnorm : N.Normal := hKnorm.comap q
  have hcardQuot : Nat.card (N ⧸ q.ker.subgroupOf N) = Nat.card K := by
    simpa [N] using
      (card_quotient_subgroupOf_comap_eq (f := q) (hf := hqsurj) (H := K))
  have hcardKerSub : Nat.card (q.ker.subgroupOf N) = Nat.card q.ker := by
    exact Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (H := q.ker) (K := N) (Subgroup.ker_le_comap (f := q) (H := K))).toEquiv
  have hcardN : Nat.card N = Nat.card K * Nat.card M := by
    have hcardN' :
        Nat.card N = Nat.card (N ⧸ q.ker.subgroupOf N) * Nat.card (q.ker.subgroupOf N) := by
      simpa using
        (Subgroup.card_eq_card_quotient_mul_card_subgroup (s := q.ker.subgroupOf N))
    calc
      Nat.card N = Nat.card (N ⧸ q.ker.subgroupOf N) * Nat.card (q.ker.subgroupOf N) := hcardN'
      _ = Nat.card K * Nat.card M := by
        rw [hcardQuot, hcardKerSub, QuotientGroup.ker_mk']
  have hNcop : Nat.Coprime p (Nat.card N) := by
    rw [hcardN]
    exact Nat.Coprime.mul_right hKcop hMcop
  have hN_le_M : N ≤ M := le_sSup ⟨hNnorm, hNcop⟩
  have hNmap_bot : N.map q = ⊥ := by
    apply (Subgroup.map_eq_bot_iff (H := N) (f := q)).2
    simpa [q, QuotientGroup.ker_mk', M] using hN_le_M
  have hK_eq : K = N.map q := by
    symm
    simpa [N] using (Subgroup.map_comap_eq_self_of_surjective (f := q) hqsurj K)
  exact hK_eq.trans hNmap_bot

/-
**Kind**: Theorem
**Note**: Lemma 1.14
**Stmt**:
Let $p$ be a prime.
Let $T$ be a $p$-subgroup of a finite group $G$.
Let $M$ be a normal $p'$-subgroup of $G$.
Let $C = C_G(T)$ and $N = N_G(T)$.
Then
\[ C_{G/M}(TM/M) = CM/M \]
and
\[ N_{G/M}(TM/M) = NM/M. \]
-/

-- Lemma 1.14 (normalizer statement)
set_option backward.isDefEq.respectTransparency false in
public theorem CFSG.normalizer_map_quotient_eq_map_normalizer
    {G : Type*} [Group G] [Finite G] (p : ℕ) [Fact p.Prime] (T M : Subgroup G)
    [Fact (IsPGroup p (↥T))] (hM : M.Normal) (hcop : Nat.Coprime p (Nat.card M)) :
    let q : G →* G ⧸ M := QuotientGroup.mk' M
    Subgroup.normalizer (T.map q) = (Subgroup.normalizer T).map q := by
  intro q
  let _ : M.Normal := hM
  have hqsurj : Function.Surjective q := QuotientGroup.mk'_surjective M
  apply (Subgroup.comap_injective hqsurj)
  rw [Subgroup.comap_normalizer_eq_of_surjective (H := T.map q) hqsurj]
  rw [QuotientGroup.comap_map_mk' (N := M) (H := T)]
  rw [QuotientGroup.comap_map_mk' (N := M) (H := Subgroup.normalizer T)]
  set K : Subgroup G := M ⊔ T
  have hM_le : M ≤ Subgroup.normalizer K := by
    exact le_trans (show M ≤ K by exact le_sup_left) Subgroup.le_normalizer
  have hnormT_le : Subgroup.normalizer T ≤ Subgroup.normalizer (K : Set G) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff] at hx ⊢
    intro y
    constructor
    · intro hyK
      have hyTK : y ∈ T ⊔ M := by simpa [K, sup_comm] using hyK
      rcases (Subgroup.mem_sup_of_normal_right (s := T) (t := M)).1 hyTK with ⟨t, ht, m, hm, htm⟩
      have ht' : x * t * x⁻¹ ∈ T := (hx t).1 ht
      have hm' : x * m * x⁻¹ ∈ M := hM.conj_mem m hm x
      have hxy : x * y * x⁻¹ = (x * t * x⁻¹) * (x * m * x⁻¹) := by
        calc
          x * y * x⁻¹ = x * (t * m) * x⁻¹ := by simp [htm]
          _ = (x * t * x⁻¹) * (x * m * x⁻¹) := by simp [mul_assoc]
      have hmemTM : x * y * x⁻¹ ∈ T ⊔ M := by
        rw [hxy]
        exact Subgroup.mul_mem_sup ht' hm'
      simpa [K, sup_comm] using hmemTM
    · intro hyK
      have hxinv : x⁻¹ ∈ Subgroup.normalizer T := by
        simpa using (Subgroup.inv_mem_iff (H := Subgroup.normalizer (T : Set G))).2 hx
      have hy' : x⁻¹ * (x * y * x⁻¹) * x ∈ K := by
        have hy'' : x⁻¹ * (x * y * x⁻¹) * x ∈ T ⊔ M := by
          have hyTK : x * y * x⁻¹ ∈ T ⊔ M := by simpa [K, sup_comm] using hyK
          rcases (Subgroup.mem_sup_of_normal_right (s := T) (t := M)).1 hyTK with ⟨t, ht, m, hm, htm⟩
          have ht' : x⁻¹ * t * x ∈ T := by
            simpa using ((Subgroup.mem_normalizer_iff).1 hxinv t).1 ht
          have hm' : x⁻¹ * m * x ∈ M := by
            simpa using hM.conj_mem m hm x⁻¹
          have hxy : x⁻¹ * (x * y * x⁻¹) * x = (x⁻¹ * t * x) * (x⁻¹ * m * x) := by
            calc
              x⁻¹ * (x * y * x⁻¹) * x = x⁻¹ * (t * m) * x := by simp [htm, mul_assoc]
              _ = (x⁻¹ * t * x) * (x⁻¹ * m * x) := by simp [mul_assoc]
          rw [hxy]
          exact Subgroup.mul_mem_sup ht' hm'
        simpa [K, sup_comm] using hy''
      simpa [mul_assoc] using hy'
  have hsup_le : M ⊔ Subgroup.normalizer T ≤ Subgroup.normalizer (K : Set G) := sup_le hM_le hnormT_le
  let T' : Subgroup K := T.subgroupOf K
  have hTp : IsPGroup p T' := by
    simpa [T'] using
      (Fact.out : IsPGroup p (↥T)).of_equiv
        ((Subgroup.subgroupOfEquivOfLe (H := T) (K := K) le_sup_right).symm)
  have hnotdvd : ¬ p ∣ T'.index := by
    let M' : Subgroup K := M.subgroupOf K
    have hM'_normal : M'.Normal := by infer_instance
    have hinf_bot : M ⊓ T = ⊥ := by
      rcases (Fact.out : IsPGroup p (↥T)).exists_card_eq with ⟨n, hn⟩
      have hcopMT : Nat.Coprime (Nat.card M) (Nat.card T) := by
        rw [hn]
        exact hcop.symm.pow_right n
      exact disjoint_iff.mp (Subgroup.disjoint_of_coprime_natCard hcopMT)
    have hdisj' : Disjoint M' T' := by
      rw [Subgroup.disjoint_def]
      intro x hxM hxT
      apply Subtype.ext
      have hxM' : (x : G) ∈ M := hxM
      have hxT' : (x : G) ∈ T := hxT
      have hxbot : (x : G) ∈ (⊥ : Subgroup G) := by
        rw [← hinf_bot]
        exact ⟨hxM', hxT'⟩
      simpa using hxbot
    have hsup' : M' ⊔ T' = ⊤ := by
      simpa [K, M', T'] using
        (Subgroup.subgroupOf_sup (A := M) (A' := T) (B := K) le_sup_left le_sup_right).symm
    have hmul' : ((M' : Set K) * (T' : Set K)) = Set.univ := by
      calc
        ((M' : Set K) * (T' : Set K)) = (↑(M' ⊔ T') : Set K) := by
          simpa using (Subgroup.normal_mul M' T').symm
        _ = Set.univ := by simp [hsup']
    have hcompl : Subgroup.IsComplement' M' T' :=
      Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdisj' hmul'
    have hindex : T'.index = Nat.card M' := hcompl.index_eq_card
    have hcardM' : Nat.card M' = Nat.card M := by
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (H := M) (K := K) le_sup_left).toEquiv
    have hcopM' : Nat.Coprime p (Nat.card M') := by
      simpa [hcardM'] using hcop
    rw [hindex]
    exact (Nat.Prime.coprime_iff_not_dvd (Fact.out : Nat.Prime p)).1 hcopM'
  let Pk : Sylow p K := IsPGroup.toSylow (p := p) hTp hnotdvd
  have hPk : (Pk : Subgroup K) = T' := by
    simp [Pk]
  let KN : Subgroup (Subgroup.normalizer (K : Set G)) := K.subgroupOf (Subgroup.normalizer (K : Set G))
  have hKN_normal : KN.Normal := by
    simpa [KN] using
      (Subgroup.normal_subgroupOf_iff_le_normalizer (H := K) (K := (Subgroup.normalizer (K : Set G)))
        (h := Subgroup.le_normalizer)).2 (le_rfl : (Subgroup.normalizer (K : Set G)) ≤ (Subgroup.normalizer (K : Set G)))
  let _ : KN.Normal := hKN_normal
  let eKN : K ≃* KN :=
    (Subgroup.subgroupOfEquivOfLe (H := K) (K := (Subgroup.normalizer (K : Set G))) Subgroup.le_normalizer).symm
  let PN : Sylow p KN := (Pk.mapSurjective (f := eKN.toMonoidHom) eKN.surjective)
  have hPmap : PN.map KN.subtype = T.subgroupOf (Subgroup.normalizer (K : Set G)) := by
    ext x
    constructor
    · intro hx
      rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
      have hy' : y ∈ (Pk : Subgroup K).map eKN.toMonoidHom := by
        change y ∈ (PN : Subgroup KN) at hy
        simpa [PN] using hy
      rcases Subgroup.mem_map.mp hy' with ⟨z, hz, rfl⟩
      have hzT' : z ∈ T' := by
        simpa [hPk] using hz
      change (z : G) ∈ T
      exact hzT'
    · intro hx
      have hxT : (x : G) ∈ T := hx
      have hxK : x ∈ K.subgroupOf (Subgroup.normalizer (K : Set G)) := by
        show (x : G) ∈ K
        exact Subgroup.mem_sup_right hxT
      let y : KN := ⟨x, hxK⟩
      let z : K := ⟨x.1, by exact Subgroup.mem_sup_right hxT⟩
      have hzT' : z ∈ T' := by
        change (z : G) ∈ T
        exact hxT
      have hzPk : z ∈ (Pk : Subgroup K) := by
        simpa [hPk] using hzT'
      have hyMap : y ∈ (Pk : Subgroup K).map eKN.toMonoidHom := by
        refine ⟨z, hzPk, ?_⟩
        ext
        rfl
      have hyPN : y ∈ PN := by
        change y ∈ (PN : Subgroup KN)
        simpa [PN] using hyMap
      exact ⟨y, hyPN, by ext; rfl⟩
  have hFr : Subgroup.normalizer (PN.map KN.subtype) ⊔ KN = ⊤ := by
    simpa using (Sylow.normalizer_sup_eq_top (p := p) (N := KN) PN)
  have hKN_le : (Subgroup.normalizer (K : Set G)) ≤ M ⊔ Subgroup.normalizer T := by
    intro x hxK
    have hFr' : Subgroup.normalizer (T.subgroupOf (Subgroup.normalizer (K : Set G))) ⊔ KN = ⊤ := by
      simpa [hPmap] using hFr
    have hxTop : (⟨x, hxK⟩ : (Subgroup.normalizer (K : Set G))) ∈ Subgroup.normalizer (T.subgroupOf (Subgroup.normalizer (K : Set G))) ⊔ KN := by
      rw [hFr']
      exact Subgroup.mem_top _
    rcases
      (Subgroup.mem_sup_of_normal_right (s := Subgroup.normalizer (T.subgroupOf (Subgroup.normalizer (K : Set G))))
        (t := KN)).1 (by exact hxTop) with ⟨a, ha, b, hb, hab⟩
    have hnorm_eq :
        Subgroup.normalizer (T.subgroupOf (Subgroup.normalizer (K : Set G))) = (Subgroup.normalizer T).subgroupOf (Subgroup.normalizer (K : Set G)) := by
      exact (Subgroup.subgroupOf_normalizer_eq (H := T) (N := (Subgroup.normalizer (K : Set G)))
        (h := le_trans le_sup_right Subgroup.le_normalizer)).symm
    have haNorm : (a : (Subgroup.normalizer (K : Set G))) ∈ (Subgroup.normalizer T).subgroupOf (Subgroup.normalizer (K : Set G)) := by
      simpa [hnorm_eq] using ha
    have haG : (a : G) ∈ M ⊔ Subgroup.normalizer T := by
      exact Subgroup.mem_sup_right (show (a : G) ∈ Subgroup.normalizer T from haNorm)
    have hT_le_target : T ≤ M ⊔ Subgroup.normalizer T := by
      exact le_trans Subgroup.le_normalizer le_sup_right
    have hK_le_target : K ≤ M ⊔ Subgroup.normalizer T := by
      exact sup_le le_sup_left hT_le_target
    have hbK : (b : G) ∈ K := hb
    have hbG : (b : G) ∈ M ⊔ Subgroup.normalizer T := hK_le_target hbK
    have hxmul : (a : G) * (b : G) = x := by
      simpa using congrArg Subtype.val hab
    rw [← hxmul]
    exact (M ⊔ Subgroup.normalizer T).mul_mem haG hbG
  exact le_antisymm hKN_le hsup_le

-- Lemma 1.14 (centralizer statement)
public theorem CFSG.centralizer_map_quotient_eq_map_centralizer
    {G : Type*} [Group G] [Finite G] (p : ℕ) [Fact p.Prime] (T M : Subgroup G)
    [Fact (IsPGroup p (↥T))] (hM : M.Normal) (hcop : Nat.Coprime p (Nat.card M)) :
    let q : G →* G ⧸ M := QuotientGroup.mk' M
    Subgroup.centralizer ((T.map q : Subgroup (G ⧸ M)) : Set (G ⧸ M)) =
      (Subgroup.centralizer (T : Set G)).map q := by
  intro q
  let _ : M.Normal := hM
  have hnormq : Subgroup.normalizer (T.map q) = (Subgroup.normalizer T).map q := by
    simpa [q] using (normalizer_map_quotient_eq_map_normalizer (G := G) (p := p) T M hM hcop)
  have hinf_bot : M ⊓ T = ⊥ := by
    rcases (Fact.out : IsPGroup p (↥T)).exists_card_eq with ⟨n, hn⟩
    have hcopMT : Nat.Coprime (Nat.card M) (Nat.card T) := by
      rw [hn]
      exact hcop.symm.pow_right n
    exact disjoint_iff.mp (Subgroup.disjoint_of_coprime_natCard hcopMT)
  refine le_antisymm ?_ ?_
  · intro x hxC
    have hconj_mem {g y : G ⧸ M}
        (hg : g ∈ Subgroup.centralizer ((T.map q : Subgroup (G ⧸ M)) : Set (G ⧸ M)))
        (hy : y ∈ T.map q) :
        g * y * g⁻¹ ∈ T.map q := by
      have hcomm := (Subgroup.mem_centralizer_iff (g := g)
        (s := ((T.map q : Subgroup (G ⧸ M)) : Set (G ⧸ M)))).1 hg y hy
      have hxy : g * y * g⁻¹ = y := by
        calc
          g * y * g⁻¹ = (g * y) * g⁻¹ := by simp [mul_assoc]
          _ = (y * g) * g⁻¹ := by rw [hcomm]
          _ = y := by simp [mul_assoc]
      simpa [hxy] using hy
    have hxN : x ∈ Subgroup.normalizer (T.map q) := by
      rw [Subgroup.mem_normalizer_iff]
      intro y
      constructor
      · intro hy
        exact hconj_mem hxC hy
      · intro hy
        have hxinvC : x⁻¹ ∈ Subgroup.centralizer ((T.map q : Subgroup (G ⧸ M)) : Set (G ⧸ M)) :=
          (Subgroup.inv_mem_iff (H := Subgroup.centralizer ((T.map q : Subgroup (G ⧸ M)) : Set (G ⧸ M)))).2 hxC
        have : x⁻¹ * (x * y * x⁻¹) * x ∈ T.map q := by
          simpa using hconj_mem hxinvC hy
        simpa [mul_assoc] using this
    rw [hnormq] at hxN
    rcases Subgroup.mem_map.mp hxN with ⟨n, hnN, rfl⟩
    have hqnC : q n ∈ Subgroup.centralizer ((T.map q : Subgroup (G ⧸ M)) : Set (G ⧸ M)) := hxC
    have hn_cent : n ∈ Subgroup.centralizer (T : Set G) := by
      rw [Subgroup.mem_centralizer_iff_commutator_eq_one]
      intro t ht
      have htmap : q t ∈ (T.map q : Subgroup (G ⧸ M)) := by
        exact ⟨t, ht, rfl⟩
      have hcomm_q : q t * q n = q n * q t :=
        (Subgroup.mem_centralizer_iff (g := q n)
          (s := ((T.map q : Subgroup (G ⧸ M)) : Set (G ⧸ M)))).1 hqnC (q t) htmap
      have hq_comm_elem : q (n * t * n⁻¹ * t⁻¹) = 1 := by
        calc
          q (n * t * n⁻¹ * t⁻¹) = q n * q t * (q n)⁻¹ * (q t)⁻¹ := by simp [mul_assoc]
          _ = q t * q n * (q n)⁻¹ * (q t)⁻¹ := by rw [hcomm_q]
          _ = 1 := by simp [mul_assoc]
      have hm_comm : n * t * n⁻¹ * t⁻¹ ∈ M := (QuotientGroup.eq_one_iff (N := M) _).1 hq_comm_elem
      have ht_norm : n * t * n⁻¹ ∈ T := ((Subgroup.mem_normalizer_iff).1 hnN t).1 ht
      have ht_comm : n * t * n⁻¹ * t⁻¹ ∈ T := T.mul_mem ht_norm (T.inv_mem ht)
      have hbot : n * t * n⁻¹ * t⁻¹ ∈ (⊥ : Subgroup G) := by
        rw [← hinf_bot]
        exact ⟨hm_comm, ht_comm⟩
      have hcomm_elem : n * t * n⁻¹ * t⁻¹ = 1 := by simpa using hbot
      have hcomm_elem' := congrArg Inv.inv hcomm_elem
      simpa [commutatorElement_def, mul_assoc] using hcomm_elem'
    exact ⟨n, hn_cent, rfl⟩
  · simpa using
      (Subgroup.map_centralizer_le_centralizer_image (s := (T : Set G)) q)

/-
**Kind**: Theorem
**Note**: Proposition 1.15
**Stmt**:
Let $G$ be a finite solvable group.
Let $p$ be a prime.
(a) If $T$ is a Sylow $p$-subgroup of $\mathcal{O}_{p',p}(G)$. Then $C_G(T) \subset \mathcal{O}_{p',p}(G)$.
(b) If $R$ is a $p$-subgroup of $G$. Then $\mathcal{O}_{p'}(C_G(R)) \subset \mathcal{O}_{p'}(G)$.
-/

-- Proposition 1.15(a)
public theorem CFSG.centralizer_sylow_subgroup_le_op_p_prime_p_of_solvable
    {G : Type*} [Group G] [Finite G] (hsolv : Group.IsSolvable G) (p : ℕ) [Fact p.Prime] :
    ∀ T : Sylow p (↥(Op_p'p p G)),
      Subgroup.centralizer ((T.1.map (Op_p'p p G).subtype : Subgroup G) : Set G) ≤ Op_p'p p G := by
  intro T
  let M : Subgroup G := pPrimeCore p G
  let q : G →* G ⧸ M := QuotientGroup.mk' M
  let TG : Subgroup G := T.1.map (Op_p'p p G).subtype
  let Tbar : Subgroup (G ⧸ M) := TG.map q
  have hqsurj : Function.Surjective q := QuotientGroup.mk'_surjective M
  have hMnormal : M.Normal := by infer_instance
  have hMcop : Nat.Coprime p (Nat.card M) := by
    simpa [M] using (pPrimeCore_coprime_card (G := G) (p := p))
  have hTG_p : IsPGroup p (↥TG) := by
    simpa [TG] using
      (IsPGroup.map (p := p) (H := (T : Subgroup (Op_p'p p G))) T.isPGroup' (Op_p'p p G).subtype)
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
      (Subgroup.map f (T : Subgroup (Op_p'p p G))).index ∣ (T : Subgroup (Op_p'p p G)).index :=
    Subgroup.index_map_dvd (H := (T : Subgroup (Op_p'p p G))) (f := f) hf_surj
  have hmapf_not_dvd : ¬ p ∣ (Subgroup.map f (T : Subgroup (Op_p'p p G))).index := by
    intro hp_dvd
    exact hT_not_dvd (hp_dvd.trans hidx_dvd)
  have hpcore_p : IsPGroup p (↥(pCore p (G ⧸ M))) := pCore_isPGroup (p := p) (G := (G ⧸ M))
  have hpow_idx :
      ∃ n, (Subgroup.map f (T : Subgroup (Op_p'p p G))).index = p ^ n := by
    exact IsPGroup.index (hG := hpcore_p) (H := Subgroup.map f (T : Subgroup (Op_p'p p G)))
  rcases hpow_idx with ⟨n, hn⟩
  have hnzero : n = 0 := by
    cases n with
    | zero =>
        rfl
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
        (⊤ : Subgroup (pCore p (G ⧸ M))).map (pCore p (G ⧸ M)).subtype = pCore p (G ⧸ M) := by
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
  have hcoreQ : pPrimeCore p (G ⧸ M) = ⊥ := by
    simpa [M] using (pPrimeCore_quotient_pPrimeCore_eq_bot (G := G) (p := p))
  let _ : Group.IsSolvable G := hsolv
  have hsolvQ : Group.IsSolvable (G ⧸ M) := by infer_instance
  have hfit_eq : fittingSubgroup (G ⧸ M) = pCore p (G ⧸ M) := Fitting_eq_pcore (G ⧸ M) p hcoreQ
  have hcent_fit :
      Subgroup.centralizer (fittingSubgroup (G ⧸ M) : Set (G ⧸ M)) ≤ fittingSubgroup (G ⧸ M) :=
    centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable (G := (G ⧸ M)) hsolvQ
  have hcent_pcore :
      Subgroup.centralizer (pCore p (G ⧸ M) : Set (G ⧸ M)) ≤ pCore p (G ⧸ M) := by
    simpa [hfit_eq] using hcent_fit
  have hcent_tbar : Subgroup.centralizer (Tbar : Set (G ⧸ M)) ≤ pCore p (G ⧸ M) := by
    simpa [hTbar_eq_pcore] using hcent_pcore
  let _ : Fact (IsPGroup p (↥TG)) := ⟨hTG_p⟩
  have hcent_map :
      Subgroup.centralizer ((TG.map q : Subgroup (G ⧸ M)) : Set (G ⧸ M)) =
        (Subgroup.centralizer (TG : Set G)).map q := by
    simpa [q] using
      (centralizer_map_quotient_eq_map_centralizer (G := G) (p := p) (T := TG) (M := M) hMnormal hMcop)
  have hmap_cent_le : (Subgroup.centralizer (TG : Set G)).map q ≤ pCore p (G ⧸ M) := by
    rw [← hcent_map]
    simpa [Tbar] using hcent_tbar
  have hcent_le_comap :
      Subgroup.centralizer (TG : Set G) ≤ Subgroup.comap q (pCore p (G ⧸ M)) :=
    (Subgroup.map_le_iff_le_comap).1 hmap_cent_le
  simpa [TG, Op_p'p, q, M] using hcent_le_comap
