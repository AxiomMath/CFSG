module

public import TauCeti.RingTheory.KrullDimension.FiniteType
public import CFSG.Mathlib.RingTheory.FinitePoints

public noncomputable section

namespace CFSG

universe u v

variable {k : Type u} [Field k]

theorem ringKrullDim_le_of_injective {A B : Type v} [CommRing A] [IsDomain A] [Algebra k A]
    [Algebra.FiniteType k A] [CommRing B] [IsDomain B] [Algebra k B] [Algebra.FiniteType k B]
    (f : A →ₐ[k] B) (hf : Function.Injective f) : ringKrullDim A ≤ ringKrullDim B := by
  rw [TauCeti.ringKrullDim_eq_toNat_trdeg k A, TauCeti.ringKrullDim_eq_toNat_trdeg k B]
  exact_mod_cast Cardinal.toNat_le_toNat (trdeg_le_of_injective f hf)
    trdeg_lt_aleph0_of_finiteType

theorem ringKrullDim_quotient_lt_of_ne_bot {A : Type v} [CommRing A] [IsDomain A] [Algebra k A]
    [Algebra.FiniteType k A] {I : Ideal A} (hI : I ≠ ⊥) :
    ringKrullDim (A ⧸ I) < ringKrullDim A := by
  obtain ⟨x, hxI, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  have hstep : ringKrullDim (A ⧸ Ideal.span {x}) + 1 ≤ ringKrullDim A :=
    ringKrullDim_quotient_succ_le_of_nonZeroDivisor (mem_nonZeroDivisors_of_ne_zero hx0)
  have hspan : Ideal.span {x} ≤ I := Ideal.span_le.mpr (by simpa using hxI)
  have hmono : ringKrullDim (A ⧸ I) ≤ ringKrullDim (A ⧸ Ideal.span {x}) :=
    ringKrullDim_le_of_surjective (Ideal.Quotient.factor hspan)
      (Ideal.Quotient.factor_surjective hspan)
  have hchain : ringKrullDim (A ⧸ I) + 1 ≤ ringKrullDim A := by
    have h1 := add_le_add_right hmono 1
    rw [add_comm 1 (ringKrullDim (A ⧸ I)), add_comm 1 (ringKrullDim (A ⧸ Ideal.span {x}))] at h1
    exact h1.trans hstep
  have htop : ringKrullDim A < ⊤ := by
    have : FiniteRingKrullDim A := TauCeti.finiteRingKrullDim_of_finiteType k A
    exact ringKrullDim_lt_top
  have h0 : (0 : WithBot ℕ∞) ≤ ringKrullDim A := ringKrullDim_nonneg_of_nontrivial
  obtain ⟨m, hm⟩ : ∃ m : ℕ, ringKrullDim A = (m : WithBot ℕ∞) := by
    generalize ringKrullDim A = z at htop h0 ⊢
    induction z using WithBot.recBotCoe with
    | bot => exact absurd h0 (by simp)
    | coe y =>
      induction y using ENat.recTopCoe with
      | top => exact absurd htop (by simp)
      | coe n => exact ⟨n, rfl⟩
  generalize hdim : ringKrullDim (A ⧸ I) = a at hchain ⊢
  induction a using WithBot.recBotCoe with
  | bot => exact lt_of_lt_of_le (WithBot.bot_lt_coe (0 : ℕ∞)) h0
  | coe y =>
    induction y using ENat.recTopCoe with
    | top =>
      have hbad : (⊤ : WithBot ℕ∞) < ⊤ := by
        simpa using hchain.trans_lt htop
      exact absurd hbad (lt_irrefl ⊤)
    | coe n =>
      rw [hm] at hchain ⊢
      have h1 : ((n : ℕ) : WithBot ℕ∞) + 1 ≤ ((m : ℕ) : WithBot ℕ∞) := by
        simpa using hchain
      rw [ENat.WithBot.add_one_le_iff] at h1
      exact_mod_cast h1

theorem ringKrullDim_le_of_finite_fiber [IsAlgClosed k] {R S : Type v} [CommRing R]
    [Algebra k R] [Algebra.FiniteType k R] [CommRing S] [IsDomain S] [Algebra k S]
    [Algebra.FiniteType k S] (φ : R →ₐ[k] S) (s : S →ₐ[k] k)
    (hfin : {s' : S →ₐ[k] k | s'.comp φ = s.comp φ}.Finite) :
    ringKrullDim S ≤ ringKrullDim R := by
  let : Algebra R S := φ.toRingHom.toAlgebra
  have : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing k R
  have : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing k S
  have halg : ∀ r : R, algebraMap R S r = φ r := fun _ => rfl
  let P : Ideal S := RingHom.ker s
  let p : Ideal R := RingHom.ker (s.comp φ)
  have hsurj : Function.Surjective s := fun c => ⟨algebraMap k S c, s.commutes c⟩
  have hsurj' : Function.Surjective (s.comp φ) := fun c => ⟨algebraMap k R c, (s.comp φ).commutes c⟩
  have hPmax : P.IsMaximal := RingHom.ker_isMaximal_of_surjective _ hsurj
  have hpmax : p.IsMaximal := RingHom.ker_isMaximal_of_surjective _ hsurj'
  have : P.LiesOver p := ⟨by
    ext r
    simp only [Ideal.mem_comap, RingHom.mem_ker, P, p, AlgHom.comp_apply, halg]⟩
  have h1 := Ideal.height_le_height_add_of_liesOver p P
  set I : Ideal S := p.map (algebraMap R S) with hI
  have hIP : I ≤ P := Ideal.map_le_iff_le_comap.mpr (Ideal.LiesOver.over (P := P) (p := p)).le
  have hpts : Finite ((S ⧸ I) →ₐ[k] k) := by
    have := hfin.to_subtype
    refine Finite.of_injective (β := {s' : S →ₐ[k] k | s'.comp φ = s.comp φ})
      (fun z => ⟨z.comp (Ideal.Quotient.mkₐ k I), ?_⟩) ?_
    · refine AlgHom.ext fun r => ?_
      have hr : r - algebraMap k R ((s.comp φ) r) ∈ p := by
        rw [RingHom.mem_ker, map_sub, AlgHom.commutes, Algebra.algebraMap_self,
          RingHom.id_apply, sub_self]
      have hmemI : φ (r - algebraMap k R ((s.comp φ) r)) ∈ I :=
        Ideal.mem_map_of_mem (algebraMap R S) hr
      have hz : ((z.comp (Ideal.Quotient.mkₐ k I)).comp φ)
          (r - algebraMap k R ((s.comp φ) r)) = 0 := by
        rw [AlgHom.comp_apply, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk,
          Ideal.Quotient.eq_zero_iff_mem.mpr hmemI, map_zero]
      rwa [map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply,
        sub_eq_zero] at hz
    · intro z₁ z₂ h
      refine AlgHom.ext fun x => ?_
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
      exact congrArg (fun t : {s' : S →ₐ[k] k | s'.comp φ = s.comp φ} => t.1 y) h
  have : Module.Finite k (S ⧸ I) := moduleFinite_of_finite_algHom (S ⧸ I)
  have : IsArtinianRing (S ⧸ I) := IsArtinianRing.of_finite k (S ⧸ I)
  have hPI : (P.map (Ideal.Quotient.mk I)).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by
      rw [Ideal.mk_ker]
      exact hIP)
  have h0 : (P.map (Ideal.Quotient.mk I)).height = 0 := by
    have hle := Ideal.height_le_ringKrullDim_of_isPrime (I := P.map (Ideal.Quotient.mk I))
    have hdim : ringKrullDim (S ⧸ I) ≤ 0 := by
      simpa using (Ring.krullDimLE_iff (n := 0) (R := S ⧸ I)).mp inferInstance
    have h' : (P.map (Ideal.Quotient.mk I)).height ≤ 0 := by
      exact_mod_cast hle.trans hdim
    exact nonpos_iff_eq_zero.mp h'
  rw [h0, add_zero] at h1
  have hPdim : (P.height : WithBot ℕ∞) = ringKrullDim S :=
    TauCeti.height_eq_ringKrullDim_of_isMaximal k P
  rw [← hPdim]
  exact (WithBot.coe_le_coe.mpr h1).trans Ideal.height_le_ringKrullDim_of_isPrime

end CFSG
