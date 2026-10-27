module

public import CFSG.Quasithin.H13.A7NatSixLocal
public import CFSG.Quasithin.H13.A7NatSchur

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.A7

open Equiv Equiv.Perm Subgroup CFSG.Open CFSG.Quasithin CFSG.Quasithin.SteinbergCB

@[expose] def cycSix (i : Fin 4) : Perm (Fin 7) :=
  swap (⟨i.1, by omega⟩ : Fin 7) (⟨i.1 + 1, by omega⟩ : Fin 7) *
    swap (⟨i.1 + 1, by omega⟩ : Fin 7) (⟨i.1 + 2, by omega⟩ : Fin 7)

theorem cycSix_sign : ∀ i, sign (cycSix i) = 1 := by
  decide

theorem cycSix_six : ∀ i, cycSix i 6 = 6 := by
  decide

@[expose] def CentSixBad (σ : Perm (Fin 7)) : Prop :=
  σ 6 = 6 ∧ (∀ i : Fin 4, ∀ k : Fin 7, σ (cycSix i k) = cycSix i (σ k)) ∧ ∃ k, σ k ≠ k

instance : DecidablePred CentSixBad := fun σ => by
  unfold CentSixBad
  infer_instance

theorem card_filter_centSixBad : (Finset.univ.filter CentSixBad).card = 0 := by
  decide +kernel

theorem centralizer_stab_six (σ : Perm (Fin 7)) (h6 : σ 6 = 6)
    (hc : ∀ i, σ * cycSix i = cycSix i * σ) : σ = 1 := by
  by_contra hne
  have hbad : CentSixBad σ := by
    refine ⟨h6, fun i k => ?_, ?_⟩
    · have := congrArg (fun τ : Perm (Fin 7) => τ k) (hc i)
      simpa [Perm.mul_apply] using this
    · by_contra hk
      push Not at hk
      exact hne (Perm.ext hk)
  have hmem : σ ∈ Finset.univ.filter CentSixBad := Finset.mem_filter.2 ⟨Finset.mem_univ _, hbad⟩
  rw [Finset.card_eq_zero.1 card_filter_centSixBad] at hmem
  exact Finset.notMem_empty _ hmem

theorem cycSix_ne_one : cycSix 0 ≠ 1 := by
  decide

section CoordAut

variable {G : Type*} [Group G] {V : Subgroup G} (ψ : V ≃* Multiplicative (evenWeight 7))

@[expose] def IsCoordAut (a : MulAut ↥V) (σ : Perm (Fin 7)) : Prop :=
  ∀ x : V, vec ψ (a x) = permAct7 σ (vec ψ x)

variable {ψ}

theorem IsCoordAut.unique {a : MulAut ↥V} {σ τ : Perm (Fin 7)} (hσ : IsCoordAut ψ a σ)
    (hτ : IsCoordAut ψ a τ) : σ = τ := by
  apply eq_of_permAct7_eq
  intro e he
  obtain ⟨x, rfl⟩ := exists_vec_eq ψ he
  rw [← hσ x, ← hτ x]

theorem isCoordAut_conjAct {n : G} (hn : n ∈ normalizer (V : Set G)) {σ : Perm (Fin 7)}
    (hσ : IsCoordAct ψ n σ) : IsCoordAut ψ (conjAct V ⟨n, hn⟩) σ :=
  fun x => hσ x _ rfl

theorem eq_of_isCoordAut {a b : MulAut ↥V} {σ : Perm (Fin 7)} (ha : IsCoordAut ψ a σ)
    (hb : IsCoordAut ψ b σ) : a = b := by
  ext x
  have h := (ha x).trans (hb x).symm
  exact congrArg Subtype.val (vec_injective ψ h)

@[expose] noncomputable def coordAutHom (A : Subgroup (MulAut ↥V))
    (hA : ∀ a ∈ A, ∃ σ, IsCoordAut ψ a σ) : A →* Perm (Fin 7) where
  toFun a := Classical.choose (hA a a.2)
  map_one' := by
    refine IsCoordAut.unique (Classical.choose_spec (hA 1 (one_mem _))) fun x => ?_
    rw [permAct7_one]
    rfl
  map_mul' a b := by
    have hab := Classical.choose_spec (hA (a * b : A) (a * b).2)
    have ha := Classical.choose_spec (hA a a.2)
    have hb := Classical.choose_spec (hA b b.2)
    refine IsCoordAut.unique hab fun x => ?_
    rw [permAct7_mul, ← hb x, ← ha]
    rfl

theorem coordAutHom_spec (A : Subgroup (MulAut ↥V)) (hA : ∀ a ∈ A, ∃ σ, IsCoordAut ψ a σ)
    (a : A) : IsCoordAut ψ (a : MulAut ↥V) (coordAutHom A hA a) :=
  Classical.choose_spec (hA a a.2)

theorem coordAutHom_injective (A : Subgroup (MulAut ↥V)) (hA : ∀ a ∈ A, ∃ σ, IsCoordAut ψ a σ) :
    Function.Injective (coordAutHom A hA) := by
  intro a b hab
  apply Subtype.ext
  apply eq_of_isCoordAut (coordAutHom_spec A hA a)
  rw [hab]
  exact coordAutHom_spec A hA b

end CoordAut

section Core

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}
  {ψ : V ≃* Multiplicative (evenWeight 7)}

theorem pCoreOf_autOn_eq_bot_six (h : A7NatPre T L V ψ) {e : V} (he : vec ψ e = vecSix)
    {X : Subgroup G} (hXV : X ≤ normalizer (V : Set G))
    (hXe : X ≤ centralizer ({(e : G)} : Set G))
    (hLeX : oTwoUpper (L ⊓ centralizer ({(e : G)} : Set G)) ≤ X) :
    pCoreOf 2 (autOn X V) = ⊥ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set A := autOn X V with hAdef
  have hA : ∀ a ∈ A, ∃ σ, IsCoordAut ψ a σ := by
    rintro a ⟨m, hm, rfl⟩
    obtain ⟨σ, hσ⟩ := h.Nact m m.2
    exact ⟨σ, isCoordAut_conjAct m.2 hσ⟩
  set ρ := coordAutHom A hA with hρ
  have hρi := coordAutHom_injective A hA
  have hfix : ∀ a : A, ρ a 6 = 6 := by
    rintro ⟨a, m, hm, rfl⟩
    have hspec := coordAutHom_spec A hA ⟨_, m, hm, rfl⟩
    have h1 := hspec e
    have h2 : (conjAct V m) e = e := by
      apply Subtype.ext
      show (m : G) * e * (m : G)⁻¹ = e
      have hme : (m : G) ∈ centralizer ({(e : G)} : Set G) := hXe hm
      rw [mem_centralizer_singleton_iff] at hme
      rw [hme, mul_inv_cancel_right]
    rw [h2, he] at h1
    exact (permAct7_vecSix_iff _).1 h1.symm
  have hstab : ∀ s ∈ stabA7 vecSix, ∃ a : A, ρ a = (s : Perm (Fin 7)) := by
    intro s hs
    rw [← natLam_map_Le_six h.L_le h.Lact h.Lonto he] at hs
    obtain ⟨l, hl, hls⟩ := hs
    rw [SetLike.mem_coe, mem_subgroupOf] at hl
    have hlX : (l : G) ∈ X := hLeX hl
    have hlN : (l : G) ∈ normalizer (V : Set G) := hXV hlX
    refine ⟨⟨conjAct V ⟨l, hlN⟩, ⟨l, hlN⟩, hlX, rfl⟩, ?_⟩
    apply IsCoordAut.unique (coordAutHom_spec A hA _)
    rw [← hls]
    exact isCoordAut_conjAct hlN (natLam_spec h.L_le h.Lact l)
  set P := pCoreOf 2 A with hPdef
  have hPA : P ≤ A := CFSG.LieType.BorelTits.pCoreOf_le 2 A
  have hPn : A ≤ normalizer (P : Set (MulAut ↥V)) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 A
  have hP2 : IsPGroup 2 P := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 A
  set Q := (P.subgroupOf A).map ρ with hQdef
  have hQ2 : IsPGroup 2 Q := (hP2.comap_of_injective _ A.subtype_injective).map ρ
  have hQn : ∀ (b : A) (q : Perm (Fin 7)), q ∈ Q → ρ b * q * (ρ b)⁻¹ ∈ Q := by
    rintro b _ ⟨x, hx, rfl⟩
    refine ⟨b * x * b⁻¹, ?_, by rw [map_mul, map_mul, map_inv]⟩
    rw [SetLike.mem_coe, mem_subgroupOf] at hx ⊢
    exact (mem_normalizer_iff.1 (hPn b.2) x).1 hx
  have hQeven : ∀ q ∈ Q, sign q = 1 → q = 1 := by
    intro q hq hqs
    have hs := isSimpleGroup_stabA7_vecSix
    set N₀ : Subgroup (stabA7 vecSix) :=
      { carrier := {s | ((s : alternatingGroup (Fin 7)) : Perm (Fin 7)) ∈ Q}
        mul_mem' := fun ha hb => Q.mul_mem ha hb
        one_mem' := Q.one_mem
        inv_mem' := fun ha => Q.inv_mem ha } with hN₀
    have hN₀n : N₀.Normal := by
      refine ⟨fun n hn g => ?_⟩
      obtain ⟨b, hb⟩ := hstab g g.2
      have := hQn b _ hn
      rw [hb] at this
      exact this
    rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal _ _ hs _ hN₀n with h0 | h0
    · have hmem : (⟨⟨q, mem_alternatingGroup.2 hqs⟩, ?_⟩ : stabA7 vecSix) ∈ N₀ := hq
      · rw [h0, mem_bot] at hmem
        exact congrArg (fun s : stabA7 vecSix => ((s : alternatingGroup (Fin 7)) :
          Perm (Fin 7))) hmem
      · obtain ⟨x, -, rfl⟩ := hq
        exact (permAct7_vecSix_iff _).2 (hfix x)
    · exfalso
      have hc : (⟨⟨cycSix 0, mem_alternatingGroup.2 (cycSix_sign 0)⟩,
          (permAct7_vecSix_iff _).2 (cycSix_six 0)⟩ : stabA7 vecSix) ∈ N₀ := h0 ▸ mem_top _
      obtain ⟨n, hn⟩ := hQ2 ⟨cycSix 0, hc⟩
      have h3 : cycSix 0 ^ 3 = 1 := by decide
      have h1 : cycSix 0 ^ 2 ^ n = 1 := congrArg Subtype.val hn
      have hord : orderOf (cycSix 0) ∣ Nat.gcd 3 (2 ^ n) :=
        Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h3) (orderOf_dvd_of_pow_eq_one h1)
      rw [show Nat.gcd 3 (2 ^ n) = 1 from Nat.Coprime.pow_right _ (by norm_num), Nat.dvd_one,
        orderOf_eq_one_iff] at hord
      exact cycSix_ne_one hord
  have hQbot : ∀ q ∈ Q, q = 1 := by
    intro q hq
    obtain ⟨x, hx, hxq⟩ := hq
    have hq6 : q 6 = 6 := by rw [← hxq]; exact hfix x
    apply centralizer_stab_six q hq6
    intro i
    obtain ⟨c, hc⟩ := hstab ⟨cycSix i, mem_alternatingGroup.2 (cycSix_sign i)⟩
      ((permAct7_vecSix_iff _).2 (cycSix_six i))
    have h1 : ρ c * q * (ρ c)⁻¹ ∈ Q := hQn c q ⟨x, hx, hxq⟩
    have h2 : q⁻¹ * (ρ c * q * (ρ c)⁻¹) ∈ Q := Q.mul_mem (Q.inv_mem ⟨x, hx, hxq⟩) h1
    have h3 := hQeven _ h2 (by simp [hc, cycSix_sign])
    rw [hc] at h3
    have h4 : cycSix i * q = q * cycSix i := by
      calc cycSix i * q = q * (q⁻¹ * (cycSix i * q * (cycSix i)⁻¹)) * cycSix i := by group
        _ = q * cycSix i := by rw [h3, mul_one]
    exact h4.symm
  rw [eq_bot_iff]
  intro a ha
  have h1 : ρ ⟨a, hPA ha⟩ = 1 :=
    hQbot _ ⟨⟨a, hPA ha⟩, by rwa [SetLike.mem_coe, mem_subgroupOf], rfl⟩
  have h2 : (⟨a, hPA ha⟩ : A) = 1 := hρi (by rw [h1, map_one])
  exact congrArg Subtype.val h2

end Core

section Coords

variable {G : Type} [Group G] {T L V : Subgroup G} {ψ : V ≃* Multiplicative (evenWeight 7)}

theorem eq_vecSix_of_weight_six {v : Fin 7 → ZMod 2} (hv : hammingNorm v = 6) (h6 : v 6 = 0) :
    v = vecSix := by
  have h1 := eq_one_of_weight_six hv h6
  funext i
  by_cases hi : i = 6
  · subst hi
    rw [h6]
    rfl
  · rw [h1 i hi]
    simp [vecSix, hi]

theorem exists_zero_of_weight_six {v : Fin 7 → ZMod 2} (hv : hammingNorm v = 6) :
    ∃ j, v j = 0 := by
  classical
  by_contra h
  push Not at h
  have h1 : (Finset.univ.filter fun i => v i ≠ 0) = Finset.univ :=
    Finset.filter_true_of_mem fun i _ => h i
  have h2 : hammingNorm v = (Finset.univ.filter fun i => v i ≠ 0).card := rfl
  rw [h1, Finset.card_univ, Fintype.card_fin] at h2
  omega

theorem A7NatPre.exists_relabel_vecSix (h : A7NatPre T L V ψ) {e : V}
    (he : hammingNorm (vec ψ e) = 6) :
    ∃ ψ' : V ≃* Multiplicative (evenWeight 7), A7NatPre T L V ψ' ∧ vec ψ' e = vecSix := by
  obtain ⟨j, hj⟩ := exists_zero_of_weight_six he
  refine ⟨ψ.trans (relabelE (swap j 6)), h.relabel _, ?_⟩
  apply eq_vecSix_of_weight_six
  · rw [hammingNorm_vec_trans_relabelE]
    exact he
  · rw [vec_trans_relabelE, permAct7_apply, swap_inv, swap_apply_right]
    exact hj

theorem isSylowTwoOf_of_le [Finite G] (hT : quasithinIsSylowTwo T) {H : Subgroup G} (hTH : T ≤ H) :
    QuasithinUnique.IsSylowTwoOf T H :=
  ⟨hTH, hT.1, fun h2 => hT.2 (h2.trans (by
    simpa [Subgroup.relIndex] using Subgroup.relIndex_dvd_index_of_le hTH))⟩

end Coords

end CFSG.Quasithin.H13.A7
