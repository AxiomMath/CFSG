module

public import CFSG.RankThree.PartOne.S12.Sec1511U5ModA
public import CFSG.RankThree.PartOne.S12.Sec1511U5Two
public import CFSG.RankThree.PartOne.KC.EvenUnitaryFiveEigen
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeSetting
public import CFSG.RankThree.PartOne.KC.UnitaryGoodSpecial
public import CFSG.RankThree.PartOne.S12.Sec1511U5Irr
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs

public section

namespace CFSG.RankThree.PartOne

namespace Sec1511

namespace U5M

open Matrix CFSG CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.RankThree.PartOne.KCEvenUnitaryFive

open scoped IsMulCommutative

variable {f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData 2 f K}

local notation "Ψ" => primeFormPsi h (isPrimeFormGram_idGram (K := K) (n := 5))
local notation "ρ" => primeFormConjHom h (idGram K 5)

theorem kfU5Irr_model (hf5 : 5 ∣ 2 ^ f + 1)
    (Ab : Subgroup (MulAut (primeFormP h (idGram K 5))))
    (hAbD : Ab ≤ primeFormD h (idGram K 5)) (hAbel : IsElementaryAbelian 5 ↥Ab)
    (hAbcard : Nat.card ↥Ab = 5 ^ 3) (xb : MulAut (primeFormP h (idGram K 5)))
    (hxb : xb ∈ Subgroup.normalizer (Ab : Set (MulAut (primeFormP h (idGram K 5)))))
    (hxb5 : xb ^ 5 = 1) (hnt : ∃ a ∈ Ab, xb * a * xb⁻¹ ≠ a)
    (Rb : Subgroup (MulAut (primeFormP h (idGram K 5)))) (hRb : IsPGroup 2 ↥Rb)
    (hAbR : Ab ≤ Subgroup.normalizer (Rb : Set (MulAut (primeFormP h (idGram K 5)))))
    (hxR : xb ∈ Subgroup.normalizer (Rb : Set (MulAut (primeFormP h (idGram K 5))))) :
    Rb = ⊥ := by
  classical
  have : Finite K := h.finite
  have hq : 3 < 2 ^ f := by
    have h1 : 5 ≤ 2 ^ f + 1 := Nat.le_of_dvd (by positivity) hf5
    omega
  have hn3 : 3 ≤ 5 := by norm_num
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot_five h hf5
  have := hAbel
  have hΨs := surjective_primeFormPsi (h := h) (n := 5) hn3 hq
  have hDn := primeFormD_normal (h := h) (n := 5) hn3 hq
  obtain ⟨g, hg⟩ := hΨs xb
  let A0 : Subgroup (primeFormUnitary h (idGram K 5)) := Ab.comap ρ
  let S : Subgroup (LinearMap.GeneralLinearGroup K (Fin 5 → K)) := A0.map (toLinU h 5)
  have hfinGU : Finite (primeFormUnitary h (idGram K 5)) := inferInstance
  have hfinA0 : Finite A0 := inferInstance
  have hSeq : A0 ≃* S := Subgroup.equivMapOfInjective A0 (toLinU h 5) toLinU_injective
  have hfinS : Finite S := Finite.of_equiv A0 hSeq.toEquiv
  have hnc : ¬ IsCyclic S := by
    intro hS
    have hA0 : IsCyclic A0 := isCyclic_of_surjective hSeq.symm.toMonoidHom hSeq.symm.surjective
    let φ : A0 →* Ab := (MonoidHom.comp ρ A0.subtype).codRestrict Ab (fun a => a.2)
    have hφ : Function.Surjective φ := by
      intro b
      obtain ⟨A, hA⟩ := hAbD b.2
      have hAm : ρ A ∈ Ab := by rw [hA]; exact b.2
      exact ⟨⟨A, hAm⟩, Subtype.ext (by exact hA)⟩
    have hAbc : IsCyclic Ab := isCyclic_of_surjective φ hφ
    obtain ⟨c, hc⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Ab)
    have h5 : c ^ 5 = 1 :=
      Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p 5 Ab) c
    have := orderOf_dvd_of_pow_eq_one h5
    rw [hc, hAbcard] at this
    norm_num at this
  have hS5 : ∀ a ∈ S, ∃ c : K, (a : Module.End K (Fin 5 → K)) ^ 5 = c • (1 : Module.End K (Fin 5 → K)) := by
    rintro _ ⟨A, hA, rfl⟩
    have h5 : (ρ A) ^ 5 = 1 := elemPow_eq_one_of_isElementaryAbelian (ρ A) (Subgroup.mem_comap.1 hA)
    have h1 : ρ (A ^ 5) = 1 := by rw [map_pow]; exact h5
    obtain ⟨c, -, hc⟩ := (primeFormConjHom_eq_one_iff hn3 hq _).1 h1
    exact ⟨c, toLinU_pow_eq_smul h hc⟩
  have hSc : ∀ a ∈ S, ∀ b ∈ S, ∃ c : K, (a : Module.End K (Fin 5 → K)) * (b : Module.End K (Fin 5 → K)) =
      c • ((b : Module.End K (Fin 5 → K)) * (a : Module.End K (Fin 5 → K))) := by
    rintro _ ⟨A, hA, rfl⟩ _ ⟨B, hB, rfl⟩
    refine exists_comm_scalar hq A B ?_
    exact congrArg Subtype.val (mul_comm (⟨ρ A, Subgroup.mem_comap.1 hA⟩ : Ab)
      ⟨ρ B, Subgroup.mem_comap.1 hB⟩)
  have hg5 : Ψ g ^ 5 = 1 := by rw [hg]; exact hxb5
  obtain ⟨hr5, c5, hc50, hc5⟩ := pow_five_data hq g hg5
  have hσ : (g.right : K →+* K) ζ = ζ := ringEquiv_fix_zeta hζ hr5
  have hXinj : Function.Injective (actL g) := act_injective g
  have hmemA0 : ∀ y : MulAut (primeFormP h (idGram K 5)),
      y ∈ Subgroup.normalizer (Ab : Set (MulAut (primeFormP h (idGram K 5)))) →
      ∀ g' : Gam h, Ψ g' = y → ∀ A, A ∈ A0 → idUAction h 5 g' A ∈ A0 := by
    intro y hy g' hg' A hA
    show ρ (idUAction h 5 g' A) ∈ Ab
    rw [← primeFormPsi_conj_primeFormConjHom, hg']
    exact (Subgroup.mem_normalizer_iff.1 hy _).1 (Subgroup.mem_comap.1 hA)
  have hn1 : ∀ a ∈ S, ∃ b ∈ S, ∀ v, (a : Module.End K (Fin 5 → K)) (actL g v) =
      actL g ((b : Module.End K (Fin 5 → K)) v) := by
    rintro _ ⟨A, hA, rfl⟩
    have hginv : Ψ g⁻¹ = xb⁻¹ := by rw [map_inv, hg]
    have hxbinv : xb⁻¹ ∈ Subgroup.normalizer
        (Ab : Set (MulAut (primeFormP h (idGram K 5)))) := (Subgroup.normalizer _).inv_mem hxb
    have hB : idUAction h 5 g⁻¹ A ∈ A0 := hmemA0 xb⁻¹ hxbinv g⁻¹ hginv A hA
    refine ⟨toLinU h 5 (idUAction h 5 g⁻¹ A), ⟨_, hB, rfl⟩, fun v => ?_⟩
    have hAB : idUAction h 5 g (idUAction h 5 g⁻¹ A) = A := by
      rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]
    rw [toLinU_apply_vec, toLinU_apply_vec, actL_apply, actL_apply,
      ← conj_rel g (idUAction h 5 g⁻¹ A) v, hAB]
  have hX5 : ∃ c : K, ∀ v, actL g (actL g (actL g (actL g (actL g v)))) = c • v :=
    ⟨c5, fun v => hc5 v⟩
  have hnt' : ∃ a ∈ S, ∃ b ∈ S, (∀ v, (b : Module.End K (Fin 5 → K)) (actL g v) =
        actL g ((a : Module.End K (Fin 5 → K)) v)) ∧
      ∀ κ : K, ¬ ∀ v, (b : Module.End K (Fin 5 → K)) v = κ • (a : Module.End K (Fin 5 → K)) v := by
    obtain ⟨a₀, ha₀, hne⟩ := hnt
    obtain ⟨A, hA⟩ := hAbD ha₀
    have hAm : A ∈ A0 := by
      show ρ A ∈ Ab
      rw [hA]
      exact ha₀
    have hB : idUAction h 5 g A ∈ A0 := hmemA0 xb hxb g hg A hAm
    refine ⟨toLinU h 5 A, ⟨A, hAm, rfl⟩, toLinU h 5 (idUAction h 5 g A), ⟨_, hB, rfl⟩,
      fun v => ?_, fun κ hκ => ?_⟩
    · rw [toLinU_apply_vec, toLinU_apply_vec, actL_apply, actL_apply]
      exact conj_rel g A v
    · have hmat : ((idUAction h 5 g A : primeFormUnitary h (idGram K 5)) : GL (Fin 5) K).val =
          κ • ((A : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) := by
        apply Matrix.toLin'.injective
        refine LinearMap.ext fun v => ?_
        have := hκ v
        rw [toLinU_apply_vec, toLinU_apply_vec] at this
        rw [Matrix.toLin'_apply, this]
        simp [Matrix.toLin'_apply]
      have h1 := conjHom_eq_of_smul hq A (idUAction h 5 g A) κ hmat
      rw [← primeFormPsi_conj_primeFormConjHom, hg, hA] at h1
      exact hne h1
  have hdim : Module.finrank K (Fin 5 → K) = 5 := Module.finrank_fin_fun K
  by_cases hRD : Rb ⊓ primeFormD h (idGram K 5) = ⊥
  ·
    by_contra hRne
    obtain ⟨r, hrR, hr2, hr1⟩ : ∃ r : MulAut (primeFormP h (idGram K 5)),
        r ∈ Rb ∧ r * r = 1 ∧ r ≠ 1 := by
      have h2dvd : 2 ∣ Nat.card Rb := by
        obtain ⟨n, hn⟩ := hRb.exists_card_eq
        have hn0 : n ≠ 0 := by
          rintro rfl
          apply hRne
          rw [pow_zero] at hn
          exact Subgroup.eq_bot_of_card_eq _ hn
        rw [hn]
        exact dvd_pow_self 2 hn0
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      obtain ⟨r0, hr0⟩ := exists_prime_orderOf_dvd_card' (G := Rb) 2 h2dvd
      refine ⟨r0, r0.2, ?_, ?_⟩
      · have := pow_orderOf_eq_one r0
        rw [hr0, pow_two] at this
        exact congrArg Subtype.val this
      · intro h1
        have : r0 = 1 := Subtype.ext h1
        rw [this, orderOf_one] at hr0
        omega
    have hcommAb : ∀ a ∈ Ab, a * r = r * a := by
      intro a ha
      have h1 : a * r * a⁻¹ * r⁻¹ ∈ Rb ⊓ primeFormD h (idGram K 5) := by
        refine ⟨?_, ?_⟩
        · exact Rb.mul_mem ((Subgroup.mem_normalizer_iff.1 (hAbR ha) r).1 hrR) (Rb.inv_mem hrR)
        · have hD : a ∈ primeFormD h (idGram K 5) := hAbD ha
          have h2 := hDn.conj_mem a⁻¹ ((primeFormD h (idGram K 5)).inv_mem hD) r
          have h3 : a * r * a⁻¹ * r⁻¹ = a * (r * a⁻¹ * r⁻¹) := by group
          rw [h3]
          exact (primeFormD h (idGram K 5)).mul_mem hD h2
      rw [hRD, Subgroup.mem_bot] at h1
      calc a * r = (a * r * a⁻¹ * r⁻¹) * (r * a) := by group
        _ = r * a := by rw [h1, one_mul]
    have hcommx : xb * r = r * xb := by
      have h1 : xb * r * xb⁻¹ * r⁻¹ ∈ Rb ⊓ primeFormD h (idGram K 5) := by
        refine ⟨?_, ?_⟩
        · exact Rb.mul_mem ((Subgroup.mem_normalizer_iff.1 hxR r).1 hrR) (Rb.inv_mem hrR)
        · have := commutator_mem_primeFormD hn3 hq xb r
          simpa [commutatorElement_def] using this
      rw [hRD, Subgroup.mem_bot] at h1
      calc xb * r = (xb * r * xb⁻¹ * r⁻¹) * (r * xb) := by group
        _ = r * xb := by rw [h1, one_mul]
    obtain ⟨gr, hgr⟩ := hΨs r
    obtain ⟨hφ2, c2, hc20, hc2⟩ := pow_two_data hq gr (by rw [hgr]; exact hr2)
    have hφ1 : gr.right ≠ 1 := by
      intro h1
      apply hr1
      have hrD : r ∈ primeFormD h (idGram K 5) := by
        rw [← hgr]
        obtain ⟨M, φ⟩ := gr
        change φ = 1 at h1
        subst h1
        exact ⟨M, by rw [primeFormConjHom_eq_primeFormPsi]⟩
      have : r ∈ Rb ⊓ primeFormD h (idGram K 5) := ⟨hrR, hrD⟩
      rw [hRD, Subgroup.mem_bot] at this
      exact this
    have hφζ : (gr.right : K →+* K) ζ ≠ ζ := invol_moves_zeta h hf5 hζ hφ2 hφ1
    have hY1 : ∀ a ∈ S, ∃ ν : K, ν ≠ 0 ∧ ∀ v, actL gr ((a : Module.End K (Fin 5 → K)) v) =
        ν • (a : Module.End K (Fin 5 → K)) (actL gr v) := by
      rintro _ ⟨A, hA, rfl⟩
      have hcomm : Ψ gr * ρ A = ρ A * Ψ gr := by
        rw [hgr]
        exact (hcommAb _ (Subgroup.mem_comap.1 hA)).symm
      obtain ⟨ν, hν0, hν⟩ := scalar_of_commute hq gr A hcomm
      refine ⟨ν, hν0, fun v => ?_⟩
      rw [toLinU_apply_vec, toLinU_apply_vec, actL_apply, actL_apply]
      exact hν v
    have hY2 : ∃ κ : K, ∀ v, actL gr (actL g v) = κ • actL g (actL gr v) := by
      have hcomm : Ψ gr * Ψ g = Ψ g * Ψ gr := by
        rw [hgr, hg]
        exact hcommx.symm
      obtain ⟨κ, hκ⟩ := commute_act hq g gr hcomm
      exact ⟨κ, fun v => hκ v⟩
    have hY3 : ∃ c : K, ∀ v, actL gr (actL gr v) = c • v := ⟨c2, fun v => hc2 v⟩
    exact U5L.fld hζ hdim hnc hS5 hSc hσ (actL g) hXinj hn1 hX5 hnt' (actL gr)
      (act_injective gr) hY1 hY2 hY3 hφζ
  ·
    exfalso
    have hR1p : IsPGroup 2 ↥(Rb ⊓ primeFormD h (idGram K 5)) := hRb.to_le inf_le_left
    let L : Subgroup (primeFormUnitary h (idGram K 5)) := (Rb ⊓ primeFormD h (idGram K 5)).comap ρ
    have hnormR1 : ∀ y ∈ Subgroup.normalizer (Rb : Set (MulAut (primeFormP h (idGram K 5)))),
        ∀ r, y * r * y⁻¹ ∈ Rb ⊓ primeFormD h (idGram K 5) ↔ r ∈ Rb ⊓ primeFormD h (idGram K 5) := by
      intro y hy r
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨(Subgroup.mem_normalizer_iff.1 hy r).2 h1, ?_⟩
        have h3 := hDn.conj_mem _ h2 y⁻¹
        have h4 : y⁻¹ * (y * r * y⁻¹) * y⁻¹⁻¹ = r := by group
        rwa [h4] at h3
      · rintro ⟨h1, h2⟩
        exact ⟨(Subgroup.mem_normalizer_iff.1 hy r).1 h1, hDn.conj_mem r h2 y⟩
    have hcL : ∀ (y : MulAut (primeFormP h (idGram K 5)))
        (c : primeFormUnitary h (idGram K 5) ≃* primeFormUnitary h (idGram K 5)),
        y ∈ Subgroup.normalizer (Rb : Set (MulAut (primeFormP h (idGram K 5)))) →
        (∀ x, ρ (c x) = y * ρ x * y⁻¹) → ∀ x, c x ∈ L ↔ x ∈ L := by
      intro y c hy hc x
      show ρ (c x) ∈ Rb ⊓ primeFormD h (idGram K 5) ↔ ρ x ∈ Rb ⊓ primeFormD h (idGram K 5)
      rw [hc x]
      exact hnormR1 y hy _
    let fL : ↥L →* ↥(Rb ⊓ primeFormD h (idGram K 5)) :=
      (MonoidHom.comp ρ L.subtype).codRestrict _ (fun x => x.2)
    have hfL : Function.Surjective fL := by
      intro r
      obtain ⟨A, hA⟩ := r.2.2
      have hAL : A ∈ L := by
        show ρ A ∈ Rb ⊓ primeFormD h (idGram K 5)
        rw [hA]
        exact r.2
      exact ⟨⟨A, hAL⟩, Subtype.ext (by exact hA)⟩
    have hker : fL.ker ≤ Subgroup.center ↥L := by
      intro x hx
      rw [Subgroup.mem_center_iff]
      intro y
      have h1 : ρ (x : primeFormUnitary h (idGram K 5)) = 1 := by
        have := congrArg Subtype.val (MonoidHom.mem_ker.1 hx)
        simpa [fL] using this
      obtain ⟨c, -, hc⟩ := (primeFormConjHom_eq_one_iff hn3 hq _).1 h1
      apply Subtype.ext
      apply Subtype.ext
      show (y : GL (Fin 5) K) * (x : GL (Fin 5) K) = (x : GL (Fin 5) K) * (y : GL (Fin 5) K)
      rw [hc]
      exact (commute_scalar c (y : GL (Fin 5) K)).eq
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have : Group.IsNilpotent ↥(Rb ⊓ primeFormD h (idGram K 5)) := hR1p.isNilpotent
    have hLnil : Group.IsNilpotent ↥L := Subgroup.isNilpotent_of_ker_le_center fL hker
    have hLeven : 2 ∣ Nat.card ↥L := by
      have h1 : 2 ∣ Nat.card ↥(Rb ⊓ primeFormD h (idGram K 5)) := by
        obtain ⟨n, hn⟩ := hR1p.exists_card_eq
        have hn0 : n ≠ 0 := by
          rintro rfl
          apply hRD
          rw [pow_zero] at hn
          exact Subgroup.eq_bot_of_card_eq _ hn
        rw [hn]
        exact dvd_pow_self 2 hn0
      exact h1.trans (Subgroup.card_dvd_of_surjective hfL)
    have hT2ne : tc L ≠ ⊥ := tc_ne_bot_of_nilpotent L hLnil hLeven
    have hT2p : IsPGroup 2 ↥(tc L) := tc_isPGroup L
    let W : Submodule K (Fin 5 → K) :=
      { carrier := {v | ∀ s ∈ tc L,
          ((s : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) *ᵥ v = v}
        add_mem' := fun {a b} ha hb s hs => by
          rw [Matrix.mulVec_add, ha s hs, hb s hs]
        zero_mem' := fun s hs => by simp
        smul_mem' := fun c v hv s hs => by
          rw [Matrix.mulVec_smul, hv s hs] }
    have hmemW : ∀ v, v ∈ W ↔ ∀ s ∈ tc L,
        ((s : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) *ᵥ v = v := fun v => Iff.rfl
    have hnormAb : ∀ A ∈ A0, (ρ A) ∈ Subgroup.normalizer
        (Rb : Set (MulAut (primeFormP h (idGram K 5)))) :=
      fun A hA => hAbR (Subgroup.mem_comap.1 hA)
    have hWS : ∀ a ∈ S, ∀ w ∈ W, (a : Module.End K (Fin 5 → K)) w ∈ W := by
      rintro _ ⟨A, hA, rfl⟩ w hw s hs
      rw [toLinU_apply_vec]
      have hAinv : (ρ A)⁻¹ ∈ Subgroup.normalizer (Rb : Set (MulAut (primeFormP h (idGram K 5)))) :=
        (Subgroup.normalizer _).inv_mem (hnormAb A hA)
      have hs' : A⁻¹ * s * A ∈ tc L := by
        have := map_tc_le L (MulAut.conj A⁻¹) (hcL (ρ A)⁻¹ (MulAut.conj A⁻¹) hAinv
          (fun x => by simp [map_mul, map_inv])) s hs
        simpa [MulAut.conj_apply] using this
      have h2 := congrArg (fun u => ((A : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) *ᵥ u)
        (hw _ hs')
      simp only [Matrix.mulVec_mulVec] at h2
      have h3 : ((A : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) *
          (((A⁻¹ * s * A : primeFormUnitary h (idGram K 5)) : GL (Fin 5) K) :
            Matrix (Fin 5) (Fin 5) K) =
          ((s : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) *
            ((A : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) := by
        have h4 : A * (A⁻¹ * s * A) = s * A := by group
        have := congrArg (fun u : primeFormUnitary h (idGram K 5) =>
          ((u : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K)) h4
        simpa only [Subgroup.coe_mul, Units.val_mul] using this
      rw [h3, ← Matrix.mulVec_mulVec] at h2
      exact h2
    have hxbinvN : xb⁻¹ ∈ Subgroup.normalizer (Rb : Set (MulAut (primeFormP h (idGram K 5)))) :=
      (Subgroup.normalizer _).inv_mem hxR
    have hWX : ∀ w ∈ W, actL g w ∈ W := by
      intro w hw s hs
      have hginv : Ψ g⁻¹ = xb⁻¹ := by rw [map_inv, hg]
      have hc : ∀ x, ρ (idUAction h 5 g⁻¹ x) = xb⁻¹ * ρ x * xb⁻¹⁻¹ := fun x => by
        rw [← primeFormPsi_conj_primeFormConjHom, hginv]
      have hb : idUAction h 5 g⁻¹ s ∈ tc L :=
        map_tc_le L (idUAction h 5 g⁻¹) (hcL xb⁻¹ _ hxbinvN hc) s hs
      have hAB : idUAction h 5 g (idUAction h 5 g⁻¹ s) = s := by
        rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]
      have h1 := conj_rel g (idUAction h 5 g⁻¹ s) w
      rw [hAB, hw _ hb] at h1
      exact h1
    have hWtop : W ≠ ⊤ := by
      intro htop
      obtain ⟨s, hs, hs1⟩ : ∃ s ∈ tc L, s ≠ 1 := by
        by_contra hcon
        push Not at hcon
        apply hT2ne
        rw [eq_bot_iff]
        intro x hx
        exact Subgroup.mem_bot.2 (hcon x hx)
      apply hs1
      apply toLinU_injective (h := h) (n := 5)
      rw [map_one]
      apply Units.ext
      refine LinearMap.ext fun v => ?_
      rw [toLinU_apply_vec, Units.val_one, Module.End.one_apply]
      have : v ∈ W := htop ▸ Submodule.mem_top
      exact this s hs
    have hWne : W ≠ ⊥ := by
      intro hbot
      let _ : MulAction (tc L) (Fin 5 → K) :=
        MulAction.compHom (Fin 5 → K) ((toLinU h 5).comp (tc L).subtype)
      have hsmul : ∀ (s : tc L) (v : Fin 5 → K),
          s • v = ((s : primeFormUnitary h (idGram K 5)).1 : Matrix (Fin 5) (Fin 5) K) *ᵥ v :=
        fun s v => toLinU_apply_vec (s : primeFormUnitary h (idGram K 5)) v
      have h0 : (0 : Fin 5 → K) ∈ MulAction.fixedPoints (tc L) (Fin 5 → K) := fun s =>
        (hsmul s 0).trans (Matrix.mulVec_zero _)
      have hdvd : 2 ∣ Nat.card (Fin 5 → K) := by
        rw [Nat.card_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin, h.card]
        exact dvd_pow (dvd_pow_self 2 (by have : 1 ≤ f := by
                                            rcases Nat.eq_zero_or_pos f with hf | hf
                                            · subst hf
                                              norm_num at hf5
                                            · exact hf
                                          omega)) (by norm_num)
      obtain ⟨b, hb, hb0⟩ :=
        hT2p.exists_fixed_point_of_prime_dvd_card_of_fixed_point (Fin 5 → K) hdvd h0
      have hbW : b ∈ W := fun s hs => (hsmul ⟨s, hs⟩ b).symm.trans (hb ⟨s, hs⟩)
      rw [hbot, Submodule.mem_bot] at hbW
      exact hb0 hbW.symm
    rcases U5L.irr hζ hdim hnc hS5 hSc hσ (actL g) hXinj hn1 hX5 hnt' W hWS hWX with h1 | h1
    · exact hWne h1
    · exact hWtop h1

end U5M

end Sec1511

end CFSG.RankThree.PartOne
