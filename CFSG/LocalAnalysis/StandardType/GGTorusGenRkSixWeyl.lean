module

public import CFSG.LocalAnalysis.StandardType.GGTorusGenRkSixLift
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitDvdAct
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLineUAct
public import CFSG.LocalAnalysis.RankThreeEvenClassification.AbelianComplementConjugacy

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.StandardType.LineU
open CFSG.LocalAnalysis.ComponentInitial

private lemma permSU_inv_rowA {K : Type} [Field K] {n d : ℕ} (hK : UnitaryFieldData 2 n K)
    (σ : Equiv.Perm (Fin d)) :
    (permSU hK σ)⁻¹ = permSU hK σ⁻¹ := by
  apply Subtype.ext
  rw [Subgroup.coe_inv]
  exact (map_inv (CFSG.RankThree.Classical.permGL (K := K)) σ).symm

private lemma exists_diag_commutator_rowA
    {d n p : ℕ} {K : Type} [Field K] (hK : UnitaryFieldData 2 n K) (hd : 3 ≤ d)
    {L' : Type} [Group L'] {φ : ↥(unitarySU 2 n K d) →* L'}
    {a : MulAut L'} {t : Fin d → K} (ha : ActsDiagU φ a t) (hap : a ^ p = 1)
    (hφker : ∀ g : ↥(unitarySU 2 n K d), φ g = 1 →
      ∃ c : K, ((g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = diagonal fun _ => c)
    (σ : Equiv.Perm (Fin d)) :
    ∃ s : ↥(unitarySU 2 n K d),
      (∃ v : Fin d → K, ((s : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = diagonal v) ∧
      s ^ p = 1 ∧ φ s = φ (permSU hK σ) * (a (φ (permSU hK σ)))⁻¹ := by
  have ha0 : ActsDiagU φ a t := ha
  obtain ⟨D, hD, hDt, hact⟩ := ha
  set P : ↥(unitarySU 2 n K d) := permSU hK σ with hP
  set s : ↥(unitarySU 2 n K d) := P * (conjN D hD P)⁻¹ with hs
  have hmat : ((s : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
      diagonal (fun k => t (σ⁻¹ k) * (t k)⁻¹) := by
    have hcoe : (s : GL (Fin d) K) = CFSG.RankThree.Classical.permGL σ *
        (D * CFSG.RankThree.Classical.permGL σ * D⁻¹)⁻¹ := by
      simp only [hs, hP, Subgroup.coe_mul, Subgroup.coe_inv, coe_conjN, coe_permSU]
    have hs_eq : (s : GL (Fin d) K) = (CFSG.RankThree.Classical.permGL σ * D *
        (CFSG.RankThree.Classical.permGL σ)⁻¹) * D⁻¹ := by
      rw [hcoe]; group
    rw [hs_eq]
    simp only [Units.val_mul, coe_permGL_matrix, coe_permGL_inv_matrix, hDt, coe_inv_diag hDt]
    rw [permMatrix_conj_diag σ t, diagonal_mul_diagonal]
  refine ⟨s, ⟨fun k => t (σ⁻¹ k) * (t k)⁻¹, hmat⟩, ?_, ?_⟩
  · have hratio : ∀ k, (t (σ⁻¹ k) * (t k)⁻¹) ^ p = 1 := fun k =>
      ActsDiagU.ratio_pow hK hd hφker ha0 hap (σ⁻¹ k) k
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, hmat, diagonal_pow]
    have hv : (fun k => t (σ⁻¹ k) * (t k)⁻¹) ^ p = fun _ => (1 : K) := by
      funext k
      exact hratio k
    rw [hv, diagonal_one, Units.val_one]
  · rw [hs, map_mul, map_inv, ← hact P]

private lemma map_aut_eq_of_center_two {L : Type*} [Group L] (Z : Subgroup L)
    (hZ : ∀ z : L, z ∈ Z ↔ z ∈ Subgroup.center L ∧ ∃ k : ℕ, z ^ 2 ^ k = 1)
    (a : MulAut L) : Z.map a.toMonoidHom = Z := by
  have hfor : ∀ (b : MulAut L) (z : L), z ∈ Z → b z ∈ Z := by
    intro b z hz
    rw [hZ] at hz ⊢
    refine ⟨?_, ?_⟩
    · rw [Subgroup.mem_center_iff] at hz ⊢
      intro g
      obtain ⟨w, rfl⟩ := b.surjective g
      rw [← map_mul, ← map_mul, hz.1 w]
    · obtain ⟨k, hk⟩ := hz.2
      exact ⟨k, by rw [← map_pow, hk, map_one]⟩
  apply le_antisymm
  · rintro _ ⟨z, hz, rfl⟩
    exact hfor a z hz
  · intro z hz
    exact ⟨a.symm z, hfor a.symm z hz, by simp⟩

theorem exists_lift_mem_normalizer_six_one
    {p : ℕ} {K : Type} [Field K]
    {M : Type} [Group M] [Finite M] {L' E : Subgroup M}
    {R : Type} [Group R] {I : Set (MulAut R)} {θ : L' ⧸ Subgroup.center L' ≃* R}
    {hE : E ≤ Subgroup.normalizer (L' : Set M)} (hpos : GGTableBPosition p L' E I θ hE) (hp : p.Prime)
    (Z : Subgroup L') [Z.Normal]
    (hZ : ∀ z : L', z ∈ Z ↔ z ∈ Subgroup.center L' ∧ ∃ k : ℕ, z ^ 2 ^ k = 1) (hp2 : p ≠ 2)
    {φ : ↥(unitarySU 2 1 K 6) →* L' ⧸ Z} (hφ : UnitTB.Model φ)
    (hdiag : ∀ e : E, ∃ (t : Fin 6 → K) (D : GL (Fin 6) K)
        (hD : D ∈ Subgroup.normalizer (unitarySU 2 1 K 6 : Set (GL (Fin 6) K))),
        (D : Matrix (Fin 6) (Fin 6) K) = diagonal t ∧
        ∀ (s : ↥(unitarySU 2 1 K 6)) (l : L'), (QuotientGroup.mk l : L' ⧸ Z) = φ s →
          (QuotientGroup.mk (L'.normalizerMonoidHom ⟨e, hE e.2⟩ l) : L' ⧸ Z) =
            φ (conjN D hD s))
    (σ : Equiv.Perm (Fin 6)) :
    ∃ n : L', (QuotientGroup.mk n : L' ⧸ Z) = φ (permSU hφ.field σ) ∧
      (n : M) ∈ Subgroup.normalizer (E : Set M) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hd6 : 3 ≤ 6 := by norm_num
  have hZp : ∀ a : MulAut L', Z.map a.toMonoidHom = Z := fun a =>
    map_aut_eq_of_center_two Z hZ a
  have hZp_mem : ∀ (a : MulAut L') (z : L'), z ∈ Z → a z ∈ Z := by
    intro a z hz
    rw [← hZp a]
    exact Subgroup.mem_map_of_mem a.toMonoidHom hz
  obtain ⟨n₀, hn₀⟩ := QuotientGroup.mk_surjective (φ (permSU hφ.field σ))
  let Zm : Subgroup M := Z.map L'.subtype
  have hZ2 : IsPGroup 2 Z := fun g => by
    obtain ⟨k, hk⟩ := ((hZ g.1).mp g.2).2
    exact ⟨k, Subtype.ext (by simpa using hk)⟩
  obtain ⟨kZ, hkZ⟩ := IsPGroup.iff_card.mp hZ2
  have key : ∀ e : E, (n₀ : M) * (e : M) * (n₀ : M)⁻¹ ∈ E ⊔ Zm := by
    intro e
    obtain ⟨t, D, hD, hDt, hacte⟩ := hdiag e
    let a_e : MulAut L' := L'.normalizerMonoidHom ⟨e, hE e.2⟩
    have heNp : (⟨e, hE e.2⟩ : ↥(Subgroup.normalizer (L' : Set M))) ^ p = 1 := by
      apply Subtype.ext
      rw [Subgroup.coe_pow, hpos.2.1.2 (e : M) e.2, Subgroup.coe_one]
    have haep : a_e ^ p = 1 := by
      rw [← map_pow, heNp, map_one]
    let ā : MulAut (L' ⧸ Z) := QuotientGroup.congr Z Z a_e (hZp a_e)
    have hā_mk : ∀ l : L', ā (QuotientGroup.mk l) = QuotientGroup.mk (a_e l) := fun l =>
      QuotientGroup.congr_mk _ _ _ _ l
    have hāpow : ∀ (l : L') (n : ℕ),
        (ā ^ n) (QuotientGroup.mk l) = QuotientGroup.mk ((a_e ^ n) l) := by
      intro l n
      induction n with
      | zero => simp
      | succ n ih =>
        rw [pow_succ', MulAut.mul_apply, ih, hā_mk, ← MulAut.mul_apply, ← pow_succ']
    have hāp : ā ^ p = 1 := by
      ext x
      obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective x
      rw [hāpow l p, haep]
      simp
    have hact : ActsDiagU φ ā t := by
      refine ⟨D, hD, hDt, fun s => ?_⟩
      obtain ⟨l, hl⟩ := QuotientGroup.mk_surjective (φ s)
      calc ā (φ s) = ā (QuotientGroup.mk l) := by rw [hl]
        _ = QuotientGroup.mk (a_e l) := hā_mk l
        _ = φ (conjN D hD s) := hacte s l hl
    obtain ⟨s, hs, hsp, hφs⟩ := exists_diag_commutator_rowA hφ.field hd6 hact hāp hφ.ker σ
    let ℓ : L' := n₀ * (a_e n₀)⁻¹
    have hℓπ : (QuotientGroup.mk ℓ : L' ⧸ Z) = φ s := by
      show (QuotientGroup.mk (n₀ * (a_e n₀)⁻¹) : L' ⧸ Z) = φ s
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, ← hā_mk n₀, hn₀, hφs]
    have hφsp : (φ s) ^ p = 1 := by rw [← map_pow, hsp, map_one]
    haveI : Fact p.Prime := ⟨hp⟩
    have hu : ∃ n : ℕ, orderOf (φ s) = p ^ n :=
      CFSG.LieType.CentralExt.exists_orderOf_eq_pow_of_pow_eq_one (n := 1) (by simpa using hφsp)
    have hpZ : ¬ p ∣ Nat.card Z := by
      rw [hkZ]
      intro hd
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hd))
    have hpZ' : ¬ p ∣ Nat.card (QuotientGroup.mk' Z).ker := by
      rw [QuotientGroup.ker_mk' Z]; exact hpZ
    obtain ⟨ℓp, hℓp_mk', hℓp_order⟩ :=
      CFSG.LieType.CentralExt.exists_pLift_aux (π := QuotientGroup.mk' Z)
        (QuotientGroup.mk'_surjective Z) hpZ' hu
    have hℓp_mk : (QuotientGroup.mk ℓp : L' ⧸ Z) = φ s := hℓp_mk'
    have hℓpE : (ℓp : M) ∈ E :=
      torus_lift_mem_E_six_one hpos hp Z hZ hp2 hdiag s hs hsp ℓp hℓp_mk hℓp_order
    have hz'mem : ℓp⁻¹ * ℓ ∈ Z := by
      rw [← (QuotientGroup.eq_one_iff (ℓp⁻¹ * ℓ))]
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, hℓp_mk, hℓπ, inv_mul_cancel]
    have hℓcom : (n₀ : M) * (e : M) * (n₀ : M)⁻¹ = (ℓ : M) * (e : M) := by
      have h1 : ((a_e n₀ : L') : M) = (e : M) * (n₀ : M) * (e : M)⁻¹ :=
        Subgroup.normalizerMonoidHom_apply_apply_coe L' ⟨e, hE e.2⟩ n₀
      have h2 : (ℓ : M) = (n₀ : M) * (((a_e n₀ : L') : M))⁻¹ := by
        simp only [ℓ, Subgroup.coe_mul, Subgroup.coe_inv]
      rw [h2, h1]
      group
    let z' : L' := ℓp⁻¹ * ℓ
    have hz'mem' : z' ∈ Z := by
      show ℓp⁻¹ * ℓ ∈ Z
      exact hz'mem
    have hℓ_eq : ℓ = ℓp * z' := by
      show ℓ = ℓp * (ℓp⁻¹ * ℓ)
      group
    have hmem : (ℓp : M) * ((z' : L') : M) * (e : M) ∈ E ⊔ Zm := by
      have h1 : (ℓp : M) ∈ E ⊔ Zm := Subgroup.mem_sup_left hℓpE
      have h2 : ((z' : L') : M) ∈ E ⊔ Zm :=
        Subgroup.mem_sup_right (Subgroup.mem_map_of_mem L'.subtype hz'mem')
      exact (E ⊔ Zm).mul_mem ((E ⊔ Zm).mul_mem h1 h2) (Subgroup.mem_sup_left e.2)
    have hgoal : (n₀ : M) * (e : M) * (n₀ : M)⁻¹ =
        (ℓp : M) * ((z' : L') : M) * (e : M) := by
      rw [hℓcom]
      conv_lhs => rw [hℓ_eq]
      rw [Subgroup.coe_mul]
    rw [hgoal]
    exact hmem
  have hE2 : IsPGroup p E := fun g => ⟨1, by
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one, pow_one]
    exact hpos.2.1.2 g.1 g.2⟩
  obtain ⟨mE, hmE⟩ := IsPGroup.iff_card.mp hE2
  have h2p : Nat.Coprime 2 p := by
    rw [Nat.coprime_comm]
    exact (hp.coprime_iff_not_dvd).mpr
      (fun hd => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hd))
  have hconjE_le : E.map (MulAut.conj (n₀ : M)).toMonoidHom ≤ E ⊔ Zm := by
    rintro x ⟨e, he, rfl⟩
    change (n₀ : M) * (e : M) * (n₀ : M)⁻¹ ∈ E ⊔ Zm
    exact key ⟨e, he⟩
  let F : Subgroup ↥(E ⊔ Zm) := E.subgroupOf (E ⊔ Zm)
  let K : Subgroup ↥(E ⊔ Zm) := Zm.subgroupOf (E ⊔ Zm)
  let S : Subgroup ↥(E ⊔ Zm) := (E.map (MulAut.conj (n₀ : M)).toMonoidHom).subgroupOf (E ⊔ Zm)
  have hcardK : Nat.card K = 2 ^ kZ := by
    have hK : K.map (E ⊔ Zm).subtype = Zm := Subgroup.map_subgroupOf_eq_of_le le_sup_right
    have hKcard : Nat.card Zm = Nat.card K :=
      (congrArg (fun H : Subgroup M => Nat.card H) hK).symm.trans
        (Subgroup.card_subtype (E ⊔ Zm) K)
    have hZmZ : Nat.card Zm = Nat.card Z := Subgroup.card_map_of_injective L'.subtype_injective
    rw [← hKcard, hZmZ, hkZ]
  have hcardF : Nat.card F = p ^ mE := by
    have hF : F.map (E ⊔ Zm).subtype = E := Subgroup.map_subgroupOf_eq_of_le le_sup_left
    have hFcard : Nat.card E = Nat.card F :=
      (congrArg (fun H : Subgroup M => Nat.card H) hF).symm.trans
        (Subgroup.card_subtype (E ⊔ Zm) F)
    rw [← hFcard, hmE]
  have hcardS : Nat.card S = Nat.card F := by
    have hS : S.map (E ⊔ Zm).subtype = E.map (MulAut.conj (n₀ : M)).toMonoidHom :=
      Subgroup.map_subgroupOf_eq_of_le hconjE_le
    have hScard : Nat.card (E.map (MulAut.conj (n₀ : M)).toMonoidHom) = Nat.card E :=
      Subgroup.card_map_of_injective (MulAut.conj (n₀ : M)).injective
    have hF : F.map (E ⊔ Zm).subtype = E := Subgroup.map_subgroupOf_eq_of_le le_sup_left
    have hFcard : Nat.card E = Nat.card F :=
      (congrArg (fun H : Subgroup M => Nat.card H) hF).symm.trans
        (Subgroup.card_subtype (E ⊔ Zm) F)
    calc Nat.card S = Nat.card (S.map (E ⊔ Zm).subtype) :=
          (Subgroup.card_subtype (E ⊔ Zm) S).symm
      _ = Nat.card (E.map (MulAut.conj (n₀ : M)).toMonoidHom) := by rw [hS]
      _ = Nat.card E := hScard
      _ = Nat.card F := hFcard
  have hE_norm : E ≤ Subgroup.normalizer (Zm : Set M) := by
    intro e he
    rw [Subgroup.mem_normalizer_iff]
    intro z
    constructor
    · intro hz
      obtain ⟨z₀, hz₀, rfl⟩ := hz
      change (e : M) * (z₀ : M) * (e : M)⁻¹ ∈ Zm
      rw [← Subgroup.normalizerMonoidHom_apply_apply_coe L' ⟨e, hE he⟩ z₀]
      exact Subgroup.mem_map_of_mem L'.subtype
        (hZp_mem (L'.normalizerMonoidHom ⟨e, hE he⟩) z₀ hz₀)
    · intro hz
      obtain ⟨w, hw, hw_eq⟩ := hz
      refine ⟨L'.normalizerMonoidHom (⟨e, hE he⟩⁻¹) w,
        hZp_mem (L'.normalizerMonoidHom (⟨e, hE he⟩⁻¹)) w hw, ?_⟩
      change (((L'.normalizerMonoidHom (⟨e, hE he⟩⁻¹) w : L') : M)) = z
      rw [Subgroup.normalizerMonoidHom_apply_apply_coe L' (⟨e, hE he⟩⁻¹) w]
      have hg : ((⟨e, hE he⟩⁻¹ : ↥(Subgroup.normalizer (L' : Set M))) : M) = (e : M)⁻¹ := by
        rw [Subgroup.coe_inv]
      rw [hg, show (w : M) = e * z * e⁻¹ from hw_eq]
      group
  have hKnorm : K.Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (H := Zm) (K := E ⊔ Zm) le_sup_right).mpr
      (sup_le hE_norm Subgroup.le_normalizer)
  haveI : K.Normal := hKnorm
  have hsupKF : K ⊔ F = ⊤ := by
    have hcd := Subgroup.codisjoint_subgroupOf_sup Zm E
    rw [sup_comm Zm E] at hcd
    exact eq_top_iff.mpr (codisjoint_iff_le_sup.mp hcd)
  have hcop0 : Nat.Coprime (2 ^ kZ) (p ^ mE) :=
    (h2p.pow_left kZ).pow_right mE
  have hcop : Nat.Coprime (Nat.card K) (Nat.card F) := by
    rw [hcardK, hcardF]; exact hcop0
  have hdisjKF : Disjoint K F := Subgroup.disjoint_of_coprime_natCard hcop
  have hfirst : K.IsComplement' F := by
    change Function.Bijective (fun x : K × F =>
      (x.1 : ↥(E ⊔ Zm)) * (x.2 : ↥(E ⊔ Zm)))
    constructor
    · intro x y hxy
      have heq : (x.1 : ↥(E ⊔ Zm))⁻¹ * (y.1 : ↥(E ⊔ Zm)) =
          (x.2 : ↥(E ⊔ Zm)) * (y.2 : ↥(E ⊔ Zm))⁻¹ := by
        have h := congrArg (fun t => (x.1 : ↥(E ⊔ Zm))⁻¹ * t) hxy
        simp only [mul_assoc, inv_mul_cancel_left] at h
        rw [h]; group
      have hmem : (x.1 : ↥(E ⊔ Zm))⁻¹ * (y.1 : ↥(E ⊔ Zm)) ∈ K ⊓ F := by
        rw [Subgroup.mem_inf]
        exact ⟨K.mul_mem (K.inv_mem x.1.2) y.1.2, heq ▸ F.mul_mem x.2.2 (F.inv_mem y.2.2)⟩
      rw [disjoint_iff.mp hdisjKF] at hmem
      have h1 : (x.1 : ↥(E ⊔ Zm))⁻¹ * (y.1 : ↥(E ⊔ Zm)) = 1 := by simpa using hmem
      have h2 : (x.2 : ↥(E ⊔ Zm)) = (y.2 : ↥(E ⊔ Zm)) := by
        have h5 : (x.2 : ↥(E ⊔ Zm)) * (y.2 : ↥(E ⊔ Zm))⁻¹ = 1 := by
          rw [← heq]; exact h1
        exact mul_inv_eq_one.mp h5
      exact Prod.ext (Subtype.ext (inv_mul_eq_one.mp h1)) (Subtype.ext h2)
    · intro g
      have hg : g ∈ K ⊔ F := by rw [hsupKF]; exact Subgroup.mem_top g
      obtain ⟨k, hk, f, hf, hkf⟩ := Subgroup.mem_sup_of_normal_left.mp hg
      exact ⟨(⟨k, hk⟩, ⟨f, hf⟩), hkf⟩
  have hcoprime : Nat.Coprime (Nat.card K) K.index := by
    rw [hfirst.symm.index_eq_card]; exact hcop
  have hcopKS : Nat.Coprime (Nat.card K) (Nat.card S) := by rw [hcardS]; exact hcop
  have hdisjKS : Disjoint K S := Subgroup.disjoint_of_coprime_natCard hcopKS
  have hsecond : K.IsComplement' S :=
    Subgroup.isComplement'_of_card_mul_and_disjoint (by rw [hcardS]; exact hfirst.card_mul_card)
      hdisjKS
  have hKcomm : IsMulCommutative K := by
    apply IsMulCommutative.of_comm
    intro a b
    apply Subtype.ext
    apply Subtype.ext
    show (a : M) * (b : M) = (b : M) * (a : M)
    obtain ⟨za, hza, hza'⟩ := Subgroup.mem_map.mp (Subgroup.mem_subgroupOf.mp a.2)
    obtain ⟨zb, hzb, hzb'⟩ := Subgroup.mem_map.mp (Subgroup.mem_subgroupOf.mp b.2)
    have hcomm : za * zb = zb * za :=
      (Subgroup.mem_center_iff.mp ((hZ za).mp hza).1 zb).symm
    calc (a : M) * (b : M) = (za : M) * (zb : M) := by
          rw [← hza', ← hzb']; rfl
      _ = ((za * zb : L') : M) := by rw [Subgroup.coe_mul]
      _ = ((zb * za : L') : M) := by rw [hcomm]
      _ = (zb : M) * (za : M) := by rw [Subgroup.coe_mul]
      _ = (b : M) * (a : M) := by
          rw [show (zb : M) = (b : M) from hzb', show (za : M) = (a : M) from hza']
  obtain ⟨y, hyK, hyconj⟩ :=
    CFSG.RankThreeEvenClassification.Helpers.abelian_normal_complements_conjugate K S F
      hKcomm hsecond hfirst hcoprime
  obtain ⟨z₀, hz₀Z, hz₀y⟩ := Subgroup.mem_map.mp (Subgroup.mem_subgroupOf.mp hyK)
  have hconjE : ∀ e : E,
      ((z₀ * n₀ : L') : M) * (e : M) * (((z₀ * n₀ : L') : M))⁻¹ ∈ E := by
    intro e
    have hs_map : (n₀ : M) * (e : M) * (n₀ : M)⁻¹ ∈
        E.map (MulAut.conj (n₀ : M)).toMonoidHom := Subgroup.mem_map_of_mem _ e.2
    have hsG : (n₀ : M) * (e : M) * (n₀ : M)⁻¹ ∈ E ⊔ Zm := hconjE_le hs_map
    let w : ↥(E ⊔ Zm) := ⟨(n₀ : M) * (e : M) * (n₀ : M)⁻¹, hsG⟩
    have hwS : w ∈ S := Subgroup.mem_subgroupOf.mpr hs_map
    have hwF : (MulAut.conj y) w ∈ F :=
      hyconj ▸ Subgroup.mem_map_of_mem (MulAut.conj y).toMonoidHom hwS
    have hval : ((MulAut.conj y) w : M) ∈ E := Subgroup.mem_subgroupOf.mp hwF
    have hval_eq : ((MulAut.conj y) w : M) =
        ((z₀ * n₀ : L') : M) * (e : M) * (((z₀ * n₀ : L') : M))⁻¹ := by
      have hwval : (w : M) = (n₀ : M) * (e : M) * (n₀ : M)⁻¹ := rfl
      simp only [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv, hwval,
        show (y : M) = (z₀ : M) from hz₀y.symm]
      group
    rwa [hval_eq] at hval
  refine ⟨z₀ * n₀, ?_, ?_⟩
  · rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff z₀).mpr hz₀Z, one_mul, hn₀]
  · rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    apply le_antisymm
    · rintro x ⟨e, he, rfl⟩
      exact hconjE ⟨e, he⟩
    · intro x hx
      let φ' : E → E := fun e =>
        ⟨((z₀ * n₀ : L') : M) * (e : M) * (((z₀ * n₀ : L') : M))⁻¹, hconjE e⟩
      have hinj : Function.Injective φ' := by
        intro a b hab
        apply Subtype.ext
        have h := congrArg Subtype.val hab
        simp only [φ'] at h
        exact mul_right_cancel (mul_left_cancel (by simpa only [mul_assoc] using h))
      have hsurj : Function.Surjective φ' := Finite.injective_iff_surjective.mp hinj
      obtain ⟨e, he⟩ := hsurj ⟨x, hx⟩
      have heval : ((z₀ * n₀ : L') : M) * (e : M) * (((z₀ * n₀ : L') : M))⁻¹ = x := by
        simpa [φ'] using congrArg Subtype.val he
      rw [← heval]
      change (MulAut.conj ((z₀ * n₀ : L') : M)) (e : M) ∈
        E.map (MulAut.conj ((z₀ * n₀ : L') : M)).toMonoidHom
      exact Subgroup.mem_map_of_mem _ e.2

end CFSG.StandardType
