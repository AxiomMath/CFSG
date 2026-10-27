module

public import CFSG.Quasithin.Background.SmithB42G2TenIso
public import CFSG.Quasithin.Background.SmithB42G2CurZorn
public import CFSG.Quasithin.Background.SmithB42G2Id

public noncomputable section

namespace CFSG.Quasithin.B42G2Ten

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Quasithin.SmithCurtis
  CFSG.Quasithin.SmithCurtis.Chev CFSG.Quasithin.B42G2Cur CFSG.Quasithin.B42G2Id
  CFSG.Quasithin.Explicit CFSG.QuasithinUnique.Setup.X7
open CFSG.LieType.Steinberg.Adjoint (xPar)


section Types

variable {K : Type} [Field K] [CharP K 2] {k : Type} [Field k] [Algebra K k] [CharP k 2] {f : ℕ}
  (ψ : ↥(adjointGroup .G2 K) →* ↥(cayleyGroup K))

abbrev tPull (lab : Fin f → G2L) : Representation k ↥(adjointGroup .G2 K) (TIdx lab → k) :=
  (matRep (tRep K k lab)).comp ψ

abbrev chiT (lab : Fin f → G2L) : ↥(adjointGroup .G2 K) → k :=
  eigval (tPull ψ lab) (tHwZ K k lab)

@[expose] def JT (lab : Fin f → G2L) : Finset (Fin Tag.G2.rank) :=
  (Finset.univ.filter fun i : Fin 2 => eExp lab i = 0 : Finset (Fin 2))

theorem tPull_dC
    (hψ : ∀ γ, IsRoot .G2 γ → ∀ c : K, ψ (xPar (rootOperatorFamily .G2) γ c) = zPsi γ c)
    (lab : Fin f → G2L) (i : Fin Tag.G2.rank) (t : Kˣ) :
    tPull ψ lab (dC .G2 K i t) (tHwZ K k lab) =
      (algebraMap K k (t : K) ^ eExp lab i) • tHwZ K k lab := by
  rw [MonoidHom.comp_apply, psi_dC ψ hψ i t]
  exact rankOne_tRep' K k lab i t

theorem chiT_dC
    (hψ : ∀ γ, IsRoot .G2 γ → ∀ c : K, ψ (xPar (rootOperatorFamily .G2) γ c) = zPsi γ c)
    (lab : Fin f → G2L) (i : Fin Tag.G2.rank) (t : Kˣ) :
    chiT ψ lab (dC .G2 K i t) = algebraMap K k (t : K) ^ eExp lab i :=
  eigval_spec (tHwZ_ne_zero K k lab) (tPull_dC ψ hψ lab i t)

theorem exists_dC_of_mem_H [Finite K] {h : ↥(adjointGroup .G2 K)} (hh : h ∈ (g2Datum K).H) :
    ∃ a b : Kˣ, h = dC .G2 K i0 a * dC .G2 K i1 b := by
  obtain ⟨e, he⟩ := torus_coords (K := K)
  have h1 : (⟨h, hh⟩ : (g2Datum K).H) = e (e.symm ⟨h, hh⟩) := (e.apply_symm_apply _).symm
  rw [fin2_eq_mulSingle (e.symm ⟨h, hh⟩), map_mul, he, he] at h1
  exact ⟨_, _, congrArg Subtype.val h1⟩

theorem isG2Type_tPull [Fintype K] (hK : Fintype.card K = 2 ^ f)
    (hψ : ∀ γ, IsRoot .G2 γ → ∀ c : K, ψ (xPar (rootOperatorFamily .G2) γ c) = zPsi γ c)
    (lab : Fin f → G2L) :
    IsG2Type (tPull ψ lab) (tHwZ K k lab) (chiT ψ lab) (JT lab) := by
  refine ⟨?_, tHwZ_ne_zero K k lab, fun h hh => ?_, fun i => ?_⟩
  · change tHwZ K k lab ∈ (g2Datum K).fixU (tPull ψ lab)
    rw [fixU_comp ψ, map_g2Datum_U ψ hψ, fixSub_zPos_tRep K k hK lab]
    exact Submodule.mem_span_singleton_self _
  · obtain ⟨a, b, rfl⟩ := exists_dC_of_mem_H hh
    have e1 : tPull ψ lab (dC .G2 K i0 a * dC .G2 K i1 b) (tHwZ K k lab) =
        (algebraMap K k (a : K) ^ eExp lab i0 * algebraMap K k (b : K) ^ eExp lab i1) •
          tHwZ K k lab := by
      rw [map_mul, Module.End.mul_apply, tPull_dC ψ hψ lab i1, map_smul, tPull_dC ψ hψ lab i0,
        smul_smul, mul_comm]
    refine e1.trans ?_
    congr 1
    exact (eigval_spec (tHwZ_ne_zero K k lab) e1).symm
  · have hh := (heckeT_comp ψ hψ (matRep (tRep K k lab)) i (tHwZ K k lab)).trans
      (hecke_tRep K k hK lab i)
    have hq := two_pow_sub_one_ne_zero hK
    have hJ : i ∈ JT lab ↔ eExp lab i = 0 :=
      (Finset.mem_filter (s := (Finset.univ : Finset (Fin 2)))
        (p := fun i : Fin 2 => eExp lab i = 0) (a := (i : Fin 2))).trans
        (and_iff_right (Finset.mem_univ _))
    change i ∈ JT lab ↔ (∀ t : Kˣ, chiT ψ lab (dC .G2 K i t) = 1) ∧
      (g2Datum K).heckeT ((matRep (tRep K k lab)).comp ψ) i (tHwZ K k lab) = 0
    rw [hh, smul_eq_zero, or_iff_left (tHwZ_ne_zero K k lab), hJ]
    simp only [chiT_dC ψ hψ, forall_pow_eq_one_iff (k := k) hK (eExp_lt lab i)]
    split_ifs with hall
    · have he := (forall_mem_roots_iff lab i).mp hall
      exact iff_of_false (fun h0 => hq (he.symm.trans h0)) fun h => one_ne_zero h.2
    · have he : eExp lab i ≠ 2 ^ f - 1 := fun h => hall ((forall_mem_roots_iff lab i).mpr h)
      exact ⟨fun h0 => ⟨Or.inl h0, rfl⟩, fun h => h.1.resolve_right he⟩

end Types

section Classification

variable {K : Type} [Field K] [CharP K 2] {k : Type} [Field k] [Algebra K k] [CharP k 2] {f : ℕ}

omit [Algebra K k] [CharP k 2] in
theorem isG2Type_congr [Finite K] {V : Type*} [AddCommGroup V] [Module k V]
    {ρ : Representation k ↥(adjointGroup .G2 K) V} {y : V} {χ χ' : ↥(adjointGroup .G2 K) → k}
    {J J' : Finset (Fin Tag.G2.rank)} (ht : IsG2Type ρ y χ J)
    (hχ : ∀ h ∈ (g2Datum K).H, χ h = χ' h) (hJ : J = J') : IsG2Type ρ y χ' J' := by
  subst hJ
  refine ⟨ht.1, ht.2.1, fun h hh => ?_, fun i => ?_⟩
  · rw [← hχ h hh]
    exact ht.2.2.1 h hh
  · have e : ∀ t : Kˣ, χ (dC .G2 K i t) = χ' (dC .G2 K i t) := fun t => hχ _ (dC_mem_H i t)
    rw [ht.2.2.2 i]
    simp only [e]

theorem g2_simple_classification [Fintype K] (hK : Fintype.card K = 2 ^ f)
    (ψ : ↥(adjointGroup .G2 K) →* ↥(cayleyGroup K))
    (hψ : ∀ γ, IsRoot .G2 γ → ∀ c : K, ψ (xPar (rootOperatorFamily .G2) γ c) = zPsi γ c)
    (hsurj : Function.Surjective ψ) {V : Type*} [AddCommGroup V] [Module k V]
    {ρ : Representation k ↥(adjointGroup .G2 K) V} (hρ : SmithCurtis.IsSimpleRep ρ) :
    ∃ lab : Fin f → G2L, ∃ β : V ≃ₗ[k] (TIdx lab → k),
      ∀ (g : ↥(adjointGroup .G2 K)) (v : V), β (ρ g v) = matRep (tRep K k lab) (ψ g) (β v) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hs : ∀ lab : Fin f → G2L, SmithCurtis.IsSimpleRep (tPull (k := k) ψ lab) := fun lab =>
    (isSimpleRep_comp_iff _ hsurj).mpr (isSimpleRep_tRep K k hK lab)
  have ht : ∀ lab : Fin f → G2L,
      IsG2Type (tPull (k := k) ψ lab) (tHwZ K k lab) (chiT ψ lab) (JT lab) :=
    fun lab => isG2Type_tPull ψ hK hψ lab
  choose μ hμ using fun lab => (ht lab).exists_mu (hs lab)
  let Φ : (Fin f → G2L) → G2TypeSet K k := fun lab => (ht lab).toTypeSet (hμ lab)
  have hΦ : Function.Injective Φ := by
    intro lab lab' h
    have hχ : ∀ g ∈ (g2Datum K).H, chiT ψ lab g = chiT ψ lab' g := fun g hg =>
      congrArg (fun p : G2TypeSet K k => ((p.1.1 ⟨g, hg⟩ : kˣ) : k)) h
    have hJ : JT lab = JT lab' := congrArg (fun p : G2TypeSet K k => p.1.2) h
    obtain ⟨β, hβ⟩ := g2_iso_of_type (hs lab) (hs lab') (ht lab)
      (isG2Type_congr (ht lab') (fun g hg => (hχ g hg).symm) hJ.symm)
    exact (tRep_iso_iff_eq hK lab lab').mp
      ⟨β, intertwines_of_comp hsurj (β := β.toLinearMap) hβ⟩
  have hcardT : Nat.card (G2TypeSet K k) = 4 ^ f := by
    rw [card_g2TypeSet (K := K) k, Nat.card_eq_fintype_card, hK, ← pow_mul, mul_comm, pow_mul]
    norm_num
  have hfin : Finite (G2TypeSet K k) := Nat.finite_of_card_ne_zero (by rw [hcardT]; positivity)
  have hcardL : Nat.card G2L = 4 := by
    rw [Nat.card_eq_fintype_card]
    rfl
  have hbij : Function.Bijective Φ := hΦ.bijective_of_nat_card_le (by
    rw [hcardT, Nat.card_fun, hcardL, Nat.card_eq_fintype_card (α := Fin f), Fintype.card_fin])
  obtain ⟨y, χ, J, hty⟩ := g2_exists_type hρ
  obtain ⟨μ₀, hμ₀⟩ := hty.exists_mu hρ
  obtain ⟨lab, hlab⟩ := hbij.2 (hty.toTypeSet hμ₀)
  have hχ : ∀ g ∈ (g2Datum K).H, χ g = chiT ψ lab g := fun g hg =>
    congrArg (fun p : G2TypeSet K k => ((p.1.1 ⟨g, hg⟩ : kˣ) : k)) hlab.symm
  have hJ : J = JT lab := congrArg (fun p : G2TypeSet K k => p.1.2) hlab.symm
  obtain ⟨β, hβ⟩ := g2_iso_of_type hρ (hs lab) (isG2Type_congr hty hχ hJ) (ht lab)
  exact ⟨lab, β, hβ⟩

theorem cayley_simple_iso_tRep [Fintype K] (hK : Fintype.card K = 2 ^ f) {V : Type*}
    [AddCommGroup V] [Module k V] {ρ : Representation k ↥(cayleyGroup K) V}
    (hρ : SmithCurtis.IsSimpleRep ρ) :
    ∃ lab : Fin f → G2L, ∃ β : V ≃ₗ[k] (TIdx lab → k),
      ∀ (g : ↥(cayleyGroup K)) (v : V), β (ρ g v) = matRep (tRep K k lab) g (β v) := by
  obtain ⟨ψ, hψ, hsurj⟩ := exists_surjective_adjointGroup_hom_cayleyGroup (F := K)
  obtain ⟨lab, β, hβ⟩ :=
    g2_simple_classification hK ψ hψ hsurj ((isSimpleRep_comp_iff ρ hsurj).mpr hρ)
  exact ⟨lab, β, intertwines_of_comp hsurj (β := β.toLinearMap) hβ⟩

end Classification

end CFSG.Quasithin.B42G2Ten
