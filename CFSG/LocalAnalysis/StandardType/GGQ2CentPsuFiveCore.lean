module

public import CFSG.LocalAnalysis.StandardType.GGQ2CentInner
public import CFSG.LocalAnalysis.StandardType.GGQTwoUnitaryCav
public import CFSG.LocalAnalysis.StandardType.GGTorusGenRkDiag
public import CFSG.LieType.CentralExt.CoprimeLift

public section

namespace CFSG.StandardType.GGQ2CentPort

open CFSG CFSG.Assembly Matrix CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial CFSG.StandardType.LineU CFSG.StandardType.UnitTB

private theorem pow_three_of_mem_diagSU {K : Type} [Field K] {d : ℕ}
    (hU : UnitaryFieldData 2 1 K) {s : ↥(unitarySU 2 1 K d)}
    (hs : ∃ v : Fin d → K,
      ((s : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = diagonal v) :
    s ^ 3 = 1 := by
  obtain ⟨v, hv⟩ := hs
  refine LineU.pow_eq_one_of_diagSU (n := 1) (d := d) (p := 3) hv ?_
  intro i
  have hgram := ((mem_unitarySU_iff hU).mp s.2).2
  rw [hv, Matrix.diagonal_map (map_zero hU.bar), Matrix.diagonal_transpose,
    Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one] at hgram
  have h1 := congrFun (congrFun hgram i) i
  simp only [Matrix.diagonal_apply_eq] at h1
  rw [UnitaryFieldData.bar_apply] at h1
  norm_num at h1
  rw [show (3 : ℕ) = 2 + 1 by norm_num, pow_succ]
  exact h1

private theorem conjN_eq_self_of_diag {d n : ℕ} {K : Type} [Field K]
    (D : GL (Fin d) K)
    (hD : D ∈ Subgroup.normalizer (unitarySU 2 n K d : Set (GL (Fin d) K)))
    {t v : Fin d → K}
    (hDt : (D : Matrix (Fin d) (Fin d) K) = diagonal t)
    (s : ↥(unitarySU 2 n K d))
    (hs : ((s : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = diagonal v) :
    conjN D hD s = s := by
  refine Subtype.ext ?_
  rw [coe_conjN]
  have hcomm : D * (s : GL (Fin d) K) = (s : GL (Fin d) K) * D := by
    refine Units.ext ?_
    simp only [Units.val_mul]
    rw [hDt, hs]
    exact Matrix.commute_diagonal t v
  rw [hcomm]
  group

theorem model_comp_of_ker_le_center {L0 R : Type} [Group L0] [Group R] {K : Type} [Field K]
    {n d : ℕ} (hd : 4 ≤ d) {ψ : ↥(unitarySU 2 n K d) →* L0} (hψ : UnitTB.Model ψ)
    {r0 : L0 →* R} (hr0 : Function.Surjective r0) (hker : r0.ker ≤ Subgroup.center L0) :
    UnitTB.Model (r0.comp ψ) := by
  classical
  have : Finite K := hψ.field.finite
  refine ⟨hψ.field, hr0.comp hψ.surj, ?_⟩
  intro g hg
  have hz : ψ g ∈ Subgroup.center L0 := hker (MonoidHom.mem_ker.mpr hg)
  have hfix : ∀ y : ↥(unitarySU 2 n K d), ψ (g * y * g⁻¹) = ψ y := by
    intro y
    have hcomm : ψ g * ψ y = ψ y * ψ g :=
      (Subgroup.mem_center_iff.mp hz (ψ y)).symm
    rw [map_mul, map_mul, map_inv]
    calc ψ g * ψ y * (ψ g)⁻¹ = ψ y * ψ g * (ψ g)⁻¹ := by rw [hcomm]
      _ = ψ y := by group
  have hK : Nat.card K = (2 ^ n) ^ 2 := by
    rw [hψ.field.card, Nat.mul_comm 2 n, pow_mul]
  exact scalar_of_map_conj_eq (φ := ψ) hψ hK hd hfix

private theorem exists_lift_mem_Bs_of_diag
    {G : Type} [Group G] {Bs L : Subgroup G}
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    {Z : Subgroup L} [Z.Normal] (hZc : Z ≤ Subgroup.center L) (hZ3 : ¬ 3 ∣ Nat.card Z)
    {K : Type} [Field K] {d : ℕ}
    {ψ : ↥(unitarySU 2 1 K d) →* L ⧸ Z} (hψ : UnitTB.Model ψ)
    (hdiag : ∀ b : ↥Bs, ∃ (t : Fin d → K) (M : GL (Fin d) K)
        (hM : M ∈ Subgroup.normalizer (unitarySU 2 1 K d : Set (GL (Fin d) K))),
        (M : Matrix (Fin d) (Fin d) K) = diagonal t ∧
        ∀ (s : ↥(unitarySU 2 1 K d)) (l : L), (QuotientGroup.mk l : L ⧸ Z) = ψ s →
          (QuotientGroup.mk (L.normalizerMonoidHom ⟨b, hN b.2⟩ l) : L ⧸ Z) =
            ψ (conjN M hM s))
    {s : ↥(unitarySU 2 1 K d)}
    (hs : ∃ v : Fin d → K,
      ((s : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = diagonal v) :
    ∃ ℓ : L, (QuotientGroup.mk ℓ : L ⧸ Z) = ψ s ∧ (ℓ : G) ∈ Bs ∧
      ∃ n : ℕ, orderOf ℓ = 3 ^ n := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hker_le_center : (QuotientGroup.mk' Z).ker ≤ Subgroup.center L := by
    rw [QuotientGroup.ker_mk']
    exact hZc
  have hnotdvd : ¬ 3 ∣ Nat.card (QuotientGroup.mk' Z).ker := by
    rwa [QuotientGroup.ker_mk']
  obtain ⟨v, hv⟩ := hs
  have hs3 : s ^ 3 = 1 := pow_three_of_mem_diagSU hψ.field ⟨v, hv⟩
  have hψs3 : ψ s ^ 3 = 1 := by simpa using congrArg ψ hs3
  obtain ⟨n₀, hn₀⟩ :=
    CFSG.LieType.CentralExt.exists_orderOf_eq_pow_of_pow_eq_one (p := 3) (n := 1)
      (by simpa using hψs3)
  obtain ⟨ℓ, hℓπ, hℓord⟩ :=
    CFSG.LieType.CentralExt.exists_pLift_aux (p := 3)
      (QuotientGroup.mk'_surjective Z) hnotdvd ⟨n₀, hn₀⟩
  have hℓπ' : (QuotientGroup.mk ℓ : L ⧸ Z) = ψ s := by
    simpa only [QuotientGroup.coe_mk'] using hℓπ
  have hℓC : (ℓ : G) ∈ Subgroup.centralizer (Bs : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    obtain ⟨t, M, hM, hMt, hact⟩ := hdiag ⟨b, hb⟩
    have hconj : conjN M hM s = s := conjN_eq_self_of_diag M hM hMt s hv
    have hact' : (QuotientGroup.mk (L.normalizerMonoidHom ⟨b, hN hb⟩ ℓ) : L ⧸ Z) =
        ψ s := by
      rw [hact s ℓ hℓπ', hconj]
    have hπeq : (QuotientGroup.mk' Z) (L.normalizerMonoidHom ⟨b, hN hb⟩ ℓ) =
        (QuotientGroup.mk' Z) ℓ := by
      rw [QuotientGroup.coe_mk']
      exact hact'.trans hℓπ'.symm
    have hℓ'ord : ∃ m : ℕ,
        orderOf (L.normalizerMonoidHom ⟨b, hN hb⟩ ℓ) = 3 ^ m :=
      CFSG.LieType.CentralExt.exists_orderOf_map_eq_pow (p := 3) (x := ℓ)
        (L.normalizerMonoidHom ⟨b, hN hb⟩).toMonoidHom hℓord
    have heq : L.normalizerMonoidHom ⟨b, hN hb⟩ ℓ = ℓ :=
      CFSG.LieType.CentralExt.eq_of_pElement hker_le_center hnotdvd hπeq hℓ'ord hℓord
    have hcoe : ((L.normalizerMonoidHom ⟨b, hN hb⟩ ℓ : L) : G) =
        b * (ℓ : G) * b⁻¹ :=
      Subgroup.normalizerMonoidHom_apply_apply_coe L ⟨b, hN hb⟩ ℓ
    calc b * (ℓ : G) = (b * (ℓ : G) * b⁻¹) * b := by group
      _ = ((L.normalizerMonoidHom ⟨b, hN hb⟩ ℓ : L) : G) * b := by rw [hcoe]
      _ = (ℓ : G) * b := by rw [heq]
  have hℓ3mem : ℓ ^ 3 ∈ Z := by
    have h1 : ℓ ^ 3 ∈ (QuotientGroup.mk' Z).ker := by
      rw [MonoidHom.mem_ker, map_pow, QuotientGroup.coe_mk', hℓπ']
      exact hψs3
    rwa [QuotientGroup.ker_mk'] at h1
  obtain ⟨n, hn⟩ := hℓord
  have hℓ3 : ℓ ^ 3 = 1 := by
    refine CFSG.LieType.CentralExt.eq_one_of_mem_ker (n := n) hnotdvd ?_ ?_
    · rwa [QuotientGroup.ker_mk']
    · rw [← pow_mul, mul_comm 3 (3 ^ n), pow_mul, ← hn, pow_orderOf_eq_one, one_pow]
  have hℓBs : (ℓ : G) ∈ Bs :=
    hSC (ℓ : G) hℓC (by simpa using congrArg Subtype.val hℓ3)
  exact ⟨ℓ, hℓπ', hℓBs, n, hn⟩

theorem toralAt_internalAt_of_quotModel
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hS : GGQTwoSetting 3 B Bs x L D J) {R : Type} [Group R] (θ : L ⧸ Subgroup.center L ≃* R)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    (Z : Subgroup L) [Z.Normal] (hZc : Z ≤ Subgroup.center L) (hZ3 : ¬ 3 ∣ Nat.card Z)
    {K : Type} [Field K] [Finite K] {d : ℕ} (hd : 5 ≤ d)
    {ψ : ↥(unitarySU 2 1 K d) →* L ⧸ Z} (hψ : UnitTB.Model ψ)
    (hdiag : ∀ b : ↥Bs, ∃ (t : Fin d → K) (M : GL (Fin d) K)
        (hM : M ∈ Subgroup.normalizer (unitarySU 2 1 K d : Set (GL (Fin d) K))),
        (M : Matrix (Fin d) (Fin d) K) = diagonal t ∧
        ∀ (s : ↥(unitarySU 2 1 K d)) (l : L), (QuotientGroup.mk l : L ⧸ Z) = ψ s →
          (QuotientGroup.mk (L.normalizerMonoidHom ⟨b, hN b.2⟩ l) : L ⧸ Z) =
            ψ (conjN M hM s)) :
    toralAt 3 B Bs x L D J hS R θ hN ∧ internalAt 3 B Bs x L D J hS R θ hN := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hLperf : commutator L = ⊤ :=
    (isQuasisimple_of_largeEvenMarking (K := L) hS.2.1).1
  have hBsE : IsElemAbelian 3 Bs := hS.1.1.2.1.2.1
  have hBsSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs :=
    hS.1.1.2.1.2.2.2
  let q : L →* R := ggQuotHom θ
  have hZker : Z ≤ q.ker := fun z hz => by
    rw [ker_ggQuotHom]
    exact hZc hz
  let r0 : L ⧸ Z →* R := QuotientGroup.lift Z q hZker
  have hr0mk : ∀ l : L, r0 (QuotientGroup.mk l) = q l := fun l =>
    QuotientGroup.lift_mk' Z hZker l
  have hr0 : Function.Surjective r0 :=
    QuotientGroup.lift_surjective_of_surjective Z q (ggQuotHom_surjective θ) hZker
  have hker0 : r0.ker ≤ Subgroup.center (L ⧸ Z) := by
    intro y hy
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective y
    have hql : q l = 1 := by rw [← hr0mk l]; exact hy
    have hlc : l ∈ Subgroup.center L := by
      rw [← ker_ggQuotHom θ, MonoidHom.mem_ker]
      exact hql
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective y
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
      Subgroup.mem_center_iff.mp hlc m]
  let Φ : ↥(unitarySU 2 1 K d) →* R := r0.comp ψ
  have hΦ : UnitTB.Model Φ := model_comp_of_ker_le_center (by omega) hψ hr0 hker0
  have hker_le_center : (QuotientGroup.mk' Z).ker ≤ Subgroup.center L := by
    rw [QuotientGroup.ker_mk']
    exact hZc
  have hnotdvd : ¬ 3 ∣ Nat.card (QuotientGroup.mk' Z).ker := by
    rwa [QuotientGroup.ker_mk']
  have hΦ_eq : ∀ (s : ↥(unitarySU 2 1 K d)) (ℓ : L),
      (QuotientGroup.mk ℓ : L ⧸ Z) = ψ s → Φ s = q ℓ := by
    intro s ℓ hℓ
    change r0 (ψ s) = q ℓ
    rw [← hℓ]
    exact hr0mk ℓ
  have hconjA : ∀ s : ↥(unitarySU 2 1 K d),
      (∃ v : Fin d → K,
        ((s : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = diagonal v) →
      MulAut.conj (Φ s) ∈ (ggBeta L θ hN).range := by
    intro s hs
    obtain ⟨ℓ, hπℓ, hℓBs, -⟩ :=
      exists_lift_mem_Bs_of_diag hBsSC hN hZc hZ3 hψ hdiag hs
    refine ⟨⟨(ℓ : G), hℓBs⟩, ?_⟩
    rw [ggBeta_eq, ggLAut_of_mem θ ℓ (hN hℓBs), hΦ_eq s ℓ hπℓ]
  have hcommOf : ∀ r : R, (∀ b ∈ (ggBeta L θ hN).range, b r = r) →
      ∀ s : ↥(unitarySU 2 1 K d),
        (∃ v : Fin d → K,
          ((s : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = diagonal v) →
        s ^ 3 = 1 → r * Φ s = Φ s * r := by
    intro r hfix s hs _
    have h1 := hfix _ (hconjA s hs)
    rw [MulAut.conj_apply] at h1
    calc r * Φ s = (Φ s * r * (Φ s)⁻¹) * Φ s := by rw [h1]
      _ = Φ s * r := by group
  have hT : toralAt 3 B Bs x L D J hS R θ hN := by
    change actionThree (ggBeta L θ hN).range
    intro r hfix _
    obtain ⟨s₀, hs₀, hΦs₀⟩ :=
      mem_diagImage_of_commute_pTorsion hΦ hd Nat.prime_three (by norm_num) r
        (hcommOf r hfix)
    have hA := hconjA s₀ hs₀
    rw [hΦs₀] at hA
    exact hA
  let U : Subgroup L := Bs.subgroupOf L
  have hUea : IsElemAbelian 3 U := by
    refine ⟨?_, ?_⟩
    · refine IsMulCommutative.of_comm fun a b => ?_
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun x : ↥Bs => (x : G))
        (hBsE.1.is_comm.comm ⟨(a : G), a.2⟩ ⟨(b : G), b.2⟩)
    · intro a ha
      apply Subtype.ext
      simpa using hBsE.2 (a : G) ha
  have hUBs : U ≤ Bs.subgroupOf L := le_rfl
  have hAea : IsElemAbelian 3 (ggBeta L θ hN).range :=
    isElemAbelian_range (fun a b => hBsE.1.is_comm.comm a b)
      (fun a => Subtype.ext (by simpa using hBsE.2 a a.2)) (ggBeta L θ hN)
  have hAcomm : ∀ a b : MulAut R, a ∈ (ggBeta L θ hN).range →
      b ∈ (ggBeta L θ hN).range → a * b = b * a := by
    intro a b ha hb
    exact congrArg Subtype.val (hAea.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hUmap : U.map ((MulAut.conj : R →* MulAut R).comp q) =
      (ggBeta L θ hN).range ⊓ (MulAut.conj : R →* MulAut R).range := by
    apply le_antisymm
    · rintro a ⟨u, hu, rfl⟩
      have hA : MulAut.conj (q u) ∈ (ggBeta L θ hN).range := by
        refine ⟨⟨(u : G), hu⟩, ?_⟩
        rw [ggBeta_eq, ggLAut_of_mem θ u (hN hu)]
      exact ⟨hA, ⟨q u, rfl⟩⟩
    · rintro a ⟨haA, ⟨r, rfl⟩⟩
      have hZ : Subgroup.center R = ⊥ := ggQ2Cent_center_eq_bot hLperf θ
      have hfix : ∀ b ∈ (ggBeta L θ hN).range, b r = r := by
        intro b hb
        have hconj : MulAut.conj (b r) = b * MulAut.conj r * b⁻¹ := by
          ext y
          simp [MulAut.conj_apply, map_mul, map_inv, mul_assoc]
        have h1 : MulAut.conj (b r) = MulAut.conj r := by
          rw [hconj, hAcomm b (MulAut.conj r) hb haA]
          group
        exact ggQ2Cent_eq_of_conj_eq hZ h1
      obtain ⟨s₀, hs₀, hΦs₀⟩ :=
        mem_diagImage_of_commute_pTorsion hΦ hd Nat.prime_three (by norm_num) r
          (hcommOf r hfix)
      obtain ⟨ℓ₀, hπℓ₀, hℓ₀Bs, -⟩ :=
        exists_lift_mem_Bs_of_diag hBsSC hN hZc hZ3 hψ hdiag hs₀
      refine Subgroup.mem_map.mpr ⟨ℓ₀, Subgroup.mem_subgroupOf.mpr hℓ₀Bs, ?_⟩
      change MulAut.conj (q ℓ₀) = MulAut.conj r
      rw [← hΦ_eq s₀ ℓ₀ hπℓ₀, hΦs₀]
  refine ⟨hT, ?_⟩
  refine ⟨U, hUea, hUBs, hUmap, ?_⟩
  intro z hz hz3
  have hqz : q z = 1 := by
    rw [← MonoidHom.mem_ker, ker_ggQuotHom]
    exact hz
  obtain ⟨g, hg⟩ := hψ.surj (QuotientGroup.mk z)
  have hΦg : Φ g = 1 := by
    change r0 (ψ g) = 1
    rw [hg, hr0mk, hqz]
  obtain ⟨c, hc⟩ := hΦ.ker g hΦg
  obtain ⟨ℓ, hπℓ, hℓBs, hℓord⟩ :=
    exists_lift_mem_Bs_of_diag hBsSC hN hZc hZ3 hψ hdiag ⟨fun _ => c, hc⟩
  have hπeq : (QuotientGroup.mk' Z) z = (QuotientGroup.mk' Z) ℓ := by
    simpa only [QuotientGroup.coe_mk'] using hg.symm.trans hπℓ.symm
  have hzord : ∃ n : ℕ, orderOf z = 3 ^ n :=
    CFSG.LieType.CentralExt.exists_orderOf_eq_pow_of_mem hz3 ⟨z, Subgroup.mem_zpowers z⟩
  have hzeq : z = ℓ :=
    CFSG.LieType.CentralExt.eq_of_pElement hker_le_center hnotdvd hπeq hzord hℓord
  rw [hzeq]
  exact Subgroup.mem_subgroupOf.mpr hℓBs

theorem toralAt_internalAt_of_diagModel
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hS : GGQTwoSetting 3 B Bs x L D J) {R : Type} [Group R] (θ : L ⧸ Subgroup.center L ≃* R)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    {K : Type} [Field K] [Finite K] {d : ℕ} (hd : 5 ≤ d)
    {ψ : ↥(unitarySU 2 1 K d) →* L} (hψ : UnitTB.Model ψ)
    (hdiag : ∀ a ∈ (ggGamma L hN).range, ∃ t : Fin d → K, ActsDiagU ψ a t) :
    toralAt 3 B Bs x L D J hS R θ hN ∧ internalAt 3 B Bs x L D J hS R θ hN := by
  classical
  let ψ' : ↥(unitarySU 2 1 K d) →* L ⧸ (⊥ : Subgroup L) :=
    (QuotientGroup.mk' (⊥ : Subgroup L)).comp ψ
  have hψ' : UnitTB.Model ψ' :=
    model_comp_of_ker_le_center (n := 1) (by omega) hψ
      (QuotientGroup.mk'_surjective ⊥) (by rw [QuotientGroup.ker_mk']; exact bot_le)
  have hZ3 : ¬ 3 ∣ Nat.card (⊥ : Subgroup L) := by
    rw [Subgroup.card_bot]
    norm_num
  have hdiag' : ∀ b : ↥Bs, ∃ (t : Fin d → K) (M : GL (Fin d) K)
      (hM : M ∈ Subgroup.normalizer (unitarySU 2 1 K d : Set (GL (Fin d) K))),
      (M : Matrix (Fin d) (Fin d) K) = diagonal t ∧
      ∀ (s : ↥(unitarySU 2 1 K d)) (l : L),
        (QuotientGroup.mk l : L ⧸ (⊥ : Subgroup L)) = ψ' s →
        (QuotientGroup.mk (L.normalizerMonoidHom ⟨b, hN b.2⟩ l) : L ⧸ (⊥ : Subgroup L)) =
          ψ' (conjN M hM s) := by
    intro b
    obtain ⟨t, M, hM, hMt, hact⟩ := hdiag (ggGamma L hN b) ⟨b, rfl⟩
    refine ⟨t, M, hM, hMt, ?_⟩
    intro s l hl
    have hl' : l = ψ s := by
      have h1 : (QuotientGroup.mk l : L ⧸ (⊥ : Subgroup L)) =
          (QuotientGroup.mk (ψ s) : L ⧸ (⊥ : Subgroup L)) := hl
      exact inv_mul_eq_one.mp (Subgroup.mem_bot.mp (QuotientGroup.eq.mp h1))
    rw [hl']
    change (QuotientGroup.mk (ggGamma L hN b (ψ s)) : L ⧸ (⊥ : Subgroup L)) =
      (QuotientGroup.mk (ψ (conjN M hM s)) : L ⧸ (⊥ : Subgroup L))
    rw [hact s]
  exact toralAt_internalAt_of_quotModel hS θ hN ⊥ bot_le hZ3 hd hψ' hdiag'

end CFSG.StandardType.GGQ2CentPort

end
