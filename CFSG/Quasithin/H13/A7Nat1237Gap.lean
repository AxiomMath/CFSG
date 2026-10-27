module

public import CFSG.Quasithin.H13.A7Nat1238Main
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.A7

open Equiv Equiv.Perm Subgroup CFSG.Open CFSG.Quasithin CFSG.Quasithin.SteinbergCB
open scoped commutatorElement

theorem perm_eq_one_or_swap_of_commute {σ : Perm (Fin 7)}
    (h1 : σ * (a5cyc012 : Perm (Fin 7)) = a5cyc012 * σ)
    (h2 : σ * (a5cyc123 : Perm (Fin 7)) = a5cyc123 * σ)
    (h3 : σ * (a5cyc234 : Perm (Fin 7)) = a5cyc234 * σ) : σ = 1 ∨ σ = swap 5 6 := by
  have e1 : ∀ x, σ ((a5cyc012 : Perm (Fin 7)) x) = (a5cyc012 : Perm (Fin 7)) (σ x) := fun x => by
    have := congrArg (fun π : Perm (Fin 7) => π x) h1
    simpa only [Perm.mul_apply] using this
  have e2 : ∀ x, σ ((a5cyc123 : Perm (Fin 7)) x) = (a5cyc123 : Perm (Fin 7)) (σ x) := fun x => by
    have := congrArg (fun π : Perm (Fin 7) => π x) h2
    simpa only [Perm.mul_apply] using this
  have e3 : ∀ x, σ ((a5cyc234 : Perm (Fin 7)) x) = (a5cyc234 : Perm (Fin 7)) (σ x) := fun x => by
    have := congrArg (fun π : Perm (Fin 7) => π x) h3
    simpa only [Perm.mul_apply] using this
  have c10 : (a5cyc012 : Perm (Fin 7)) 0 = 1 := by decide
  have c11 : (a5cyc012 : Perm (Fin 7)) 1 = 2 := by decide
  have c22 : (a5cyc123 : Perm (Fin 7)) 2 = 3 := by decide
  have c23 : (a5cyc123 : Perm (Fin 7)) 3 = 1 := by decide
  have c33 : (a5cyc234 : Perm (Fin 7)) 3 = 4 := by decide
  have s1 : σ 1 = (a5cyc012 : Perm (Fin 7)) (σ 0) := by rw [← c10, e1]
  have s2 : σ 2 = (a5cyc012 : Perm (Fin 7)) (σ 1) := by rw [← c11, e1]
  have s3 : σ 3 = (a5cyc123 : Perm (Fin 7)) (σ 2) := by rw [← c22, e2]
  have s1' : σ 1 = (a5cyc123 : Perm (Fin 7)) (σ 3) := by rw [← c23, e2]
  have s4 : σ 4 = (a5cyc234 : Perm (Fin 7)) (σ 3) := by rw [← c33, e3]
  have hne : σ 1 ≠ σ 0 := fun h => absurd (σ.injective h) (by decide)
  have key : ∀ a : Fin 7, (a5cyc012 : Perm (Fin 7)) a ≠ a →
      (a5cyc012 : Perm (Fin 7)) a = (a5cyc123 : Perm (Fin 7)) ((a5cyc123 : Perm (Fin 7))
        ((a5cyc012 : Perm (Fin 7)) ((a5cyc012 : Perm (Fin 7)) a))) → a = 0 := by
    decide
  have h0 : σ 0 = 0 := key (σ 0) (by rw [← s1]; exact hne) (by rw [← s1, ← s2, ← s3, ← s1'])
  have hs1 : σ 1 = 1 := by rw [s1, h0]; decide
  have hs2 : σ 2 = 2 := by rw [s2, hs1]; decide
  have hs3 : σ 3 = 3 := by rw [s3, hs2]; decide
  have hs4 : σ 4 = 4 := by rw [s4, hs3]; decide
  have hlow : ∀ i : Fin 7, (i : ℕ) < 5 → σ i = i := by
    intro i hi
    have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
    rcases this with rfl | rfl | rfl | rfl | rfl
    · exact h0
    · exact hs1
    · exact hs2
    · exact hs3
    · exact hs4
  have hhigh : ∀ j : Fin 7, 5 ≤ (j : ℕ) → 5 ≤ (σ j : ℕ) := by
    intro j hj
    by_contra hlt
    push Not at hlt
    have h1 : σ (σ j) = σ j := hlow (σ j) hlt
    have h2 : σ j = j := σ.injective h1
    rw [h2] at hlt
    omega
  have h56 : σ 5 ≠ σ 6 := fun h => absurd (σ.injective h) (by decide)
  have hv : ∀ j : Fin 7, 5 ≤ (j : ℕ) → j = 5 ∨ j = 6 := by decide
  have hv5 := hv (σ 5) (hhigh 5 (by decide))
  have hv6 := hv (σ 6) (hhigh 6 (by decide))
  have hall : ∀ i : Fin 7, i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 := by decide
  rcases hv5 with h5' | h5'
  · left
    have h6' : σ 6 = 6 := by
      rcases hv6 with h | h
      · exact absurd (h5'.trans h.symm) h56
      · exact h
    ext i
    rcases hall i with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [h0]; rfl
    · rw [hs1]; rfl
    · rw [hs2]; rfl
    · rw [hs3]; rfl
    · rw [hs4]; rfl
    · rw [h5']; rfl
    · rw [h6']; rfl
  · right
    have h6' : σ 6 = 5 := by
      rcases hv6 with h | h
      · exact h
      · exact absurd (h5'.trans h.symm) h56
    ext i
    rcases hall i with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [h0]; decide
    · rw [hs1]; decide
    · rw [hs2]; decide
    · rw [hs3]; decide
    · rw [hs4]; decide
    · rw [h5']; decide
    · rw [h6']; decide

theorem not_commute_swap_of_lt_five : ∀ p q : Fin 7, p ≠ q → (p : ℕ) < 5 → (q : ℕ) < 5 →
    ¬ (swap p q * (a5cyc012 : Perm (Fin 7)) = a5cyc012 * swap p q ∧
      swap p q * (a5cyc123 : Perm (Fin 7)) = a5cyc123 * swap p q ∧
      swap p q * (a5cyc234 : Perm (Fin 7)) = a5cyc234 * swap p q) := by
  decide

@[expose] def dbl0516 : alternatingGroup (Fin 7) :=
  ⟨swap 0 5 * swap 1 6, by rw [mem_alternatingGroup]; decide⟩

theorem dbl0516_conj_swap :
    (dbl0516 : Perm (Fin 7)) * swap 5 6 * (dbl0516 : Perm (Fin 7))⁻¹ = swap 0 1 := by
  decide

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem isElemAbelian_map_conj {A : Subgroup G} (hA : IsElemAbelian 2 A) (g : G) :
    IsElemAbelian 2 (A.map (MulAut.conj g).toMonoidHom) := CFSG.Open.IsElemAbelian.map hA _

variable {T L V : Subgroup G} {ψ : V ≃* Multiplicative (evenWeight 7)}

theorem Kv_eq_commutator_of_not_le (hyp : Hyp1223 G T L V) (h : A7NatPre T L V ψ) {e : V}
    (he : vec ψ e = vecFS) {X : Subgroup G} (hXK : X ≤ normalizer (Kv hyp e : Set G))
    (hX : ¬ ⁅Kv hyp e, X⁆ ≤ centralizer (V : Set G)) : Kv hyp e = ⁅Kv hyp e, X⁆ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKL : Kv hyp e ≤ L := Kv_le_L hyp e
  have hNK : ⁅Kv hyp e, X⁆ ≤ Kv hyp e := (le_normalizer_iff_commutator_le_left).1 hXK
  have hKN : Kv hyp e ≤ normalizer ((⁅Kv hyp e, X⁆ : Subgroup G) : Set G) :=
    normalizer_commutator_ge_left (Kv hyp e) X
  have hPV := pCoreOf_Kv_le_centralizer hyp h he
  obtain ⟨hq, -⟩ := Kv_quasisimple hyp h he
  have hNKn : ((⁅Kv hyp e, X⁆ : Subgroup G).subgroupOf (Kv hyp e)).Normal :=
    (normal_subgroupOf_iff_le_normalizer hNK).2 hKN
  have hNq : (((⁅Kv hyp e, X⁆ : Subgroup G).subgroupOf (Kv hyp e)).map
      (QuotientGroup.mk' (CFSG.pCore 2 ↥(Kv hyp e)))).Normal :=
    hNKn.map _ (QuotientGroup.mk'_surjective _)
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hq hNq with h1 | h1
  ·
    refine le_antisymm ?_ hNK
    have h2 : IsPGroup 2 (↥(Kv hyp e) ⧸ (⁅Kv hyp e, X⁆ : Subgroup G).subgroupOf (Kv hyp e)) := by
      intro q
      obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective q
      have hk : QuotientGroup.mk' (CFSG.pCore 2 ↥(Kv hyp e)) k ∈
          ((⁅Kv hyp e, X⁆ : Subgroup G).subgroupOf (Kv hyp e)).map
            (QuotientGroup.mk' (CFSG.pCore 2 ↥(Kv hyp e))) := h1 ▸ mem_top _
      obtain ⟨n, hn, hnk⟩ := hk
      have hp : n⁻¹ * k ∈ CFSG.pCore 2 ↥(Kv hyp e) := by
        rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hnk
        exact hnk
      obtain ⟨m, hm⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥(Kv hyp e))) ⟨_, hp⟩
      refine ⟨m, ?_⟩
      have hq1 : (QuotientGroup.mk k : ↥(Kv hyp e) ⧸
          (⁅Kv hyp e, X⁆ : Subgroup G).subgroupOf (Kv hyp e)) = QuotientGroup.mk (n⁻¹ * k) := by
        rw [QuotientGroup.eq]
        have := hNKn.conj_mem _ (inv_mem hn) k⁻¹
        simpa [mul_assoc] using this
      have hm' : (n⁻¹ * k) ^ 2 ^ m = 1 := by
        have := congrArg Subtype.val hm
        simpa using this
      rw [hq1, ← QuotientGroup.mk_pow, hm', QuotientGroup.mk_one]
    have h3 := eq_top_of_perfect_of_isPGroup (Kv_perfect hyp e)
      ((⁅Kv hyp e, X⁆ : Subgroup G).subgroupOf (Kv hyp e)) h2
    intro k hk
    have : (⟨k, hk⟩ : ↥(Kv hyp e)) ∈ (⁅Kv hyp e, X⁆ : Subgroup G).subgroupOf (Kv hyp e) :=
      h3 ▸ mem_top _
    exact this
  ·
    exfalso
    apply hX
    intro n hn
    have hnK : n ∈ Kv hyp e := hNK hn
    have hnL : n ∈ L := hKL hnK
    have hz : (QuotientGroup.mk ⟨n, hnK⟩ : ↥(Kv hyp e) ⧸ CFSG.pCore 2 ↥(Kv hyp e)) ∈
        center (↥(Kv hyp e) ⧸ CFSG.pCore 2 ↥(Kv hyp e)) := h1 ⟨⟨n, hnK⟩, hn, rfl⟩
    have hcom : ∀ τ ∈ altFive, (τ : alternatingGroup (Fin 7)) * natLam h.L_le h.Lact ⟨n, hnL⟩ =
        natLam h.L_le h.Lact ⟨n, hnL⟩ * τ := by
      intro τ hτ
      obtain ⟨k, hkK, hk⟩ := exists_mem_Kv_natLam hyp h he hτ
      have hc := mem_center_iff.1 hz (QuotientGroup.mk ⟨(k : G), hkK⟩)
      have hkn : (⟨(k : G), hkK⟩ : ↥(Kv hyp e)) * ⟨n, hnK⟩ * (⟨(k : G), hkK⟩ : ↥(Kv hyp e))⁻¹ *
          (⟨n, hnK⟩ : ↥(Kv hyp e))⁻¹ ∈ CFSG.pCore 2 ↥(Kv hyp e) := by
        rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
          QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_inv, hc]
        group
      have hknV : (k : G) * n * (k : G)⁻¹ * n⁻¹ ∈ centralizer (V : Set G) := by
        apply hPV
        rw [pCoreOf_eq_map_cfsgPCore]
        exact ⟨_, hkn, rfl⟩
      have h4 : natLam h.L_le h.Lact (k * ⟨n, hnL⟩ * k⁻¹ * ⟨n, hnL⟩⁻¹) = 1 :=
        (natLam_eq_one_iff h.L_le h.Lact _).2 hknV
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hk] at h4
      calc τ * natLam h.L_le h.Lact ⟨n, hnL⟩
          = (τ * natLam h.L_le h.Lact ⟨n, hnL⟩ * τ⁻¹ * (natLam h.L_le h.Lact ⟨n, hnL⟩)⁻¹) *
            (natLam h.L_le h.Lact ⟨n, hnL⟩ * τ) := by group
        _ = natLam h.L_le h.Lact ⟨n, hnL⟩ * τ := by rw [h4, one_mul]
    have hmem : natLam h.L_le h.Lact ⟨n, hnL⟩ ∈ altFive := by
      rw [← natLam_map_Kv hyp h he]
      exact ⟨⟨n, hnL⟩, hnK, rfl⟩
    have hz' : (⟨natLam h.L_le h.Lact ⟨n, hnL⟩, hmem⟩ : altFive) ∈ center altFive := by
      rw [mem_center_iff]
      intro τ
      exact Subtype.ext (hcom τ τ.2)
    rw [center_altFive, mem_bot] at hz'
    have h5 : natLam h.L_le h.Lact ⟨n, hnL⟩ = 1 := congrArg Subtype.val hz'
    exact (natLam_eq_one_iff h.L_le h.Lact _).1 h5

theorem gap1237KeJ_of (h1222 : Stmt12_2_2) (h331 : Stmt3_3_1) (h1229 : Stmt12_2_9) :
    Gap1237KeJ := by
  intro G _ _ T L V hyp ψ₀ e hS
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases h1222 G T hyp.simple hyp.nonabelian hyp.qtke hyp.sylow with hAlt | h3
  · exact absurd hAlt hyp.notAlt
  obtain ⟨-, -, hall⟩ := h3 L hyp.maximal hyp.faithful hyp.quasisimple
  obtain ⟨⟨hVT, hTV, -, -⟩, hTI, -, -⟩ := hall V hyp.irrPlus
  have hLV : L ≤ normalizer (V : Set G) := hyp.irrPlus.2.2.1
  have hNM := normalizer_le_of_hyp1223 h331 hyp hVT hTV
  have hpre : A7NatPre T L V ψ₀ :=
    ⟨hVT, hLV, hTV, hS.act, hS.onto, nact_of_lact hLV hS.act hS.onto hNM, hNM, hTI⟩
  obtain ⟨ψ, h, he, -⟩ := hpre.exists_relabel_vecFS hS.weight
  have hZC : quasithinOmegaOneCenter T ≤ centralizer (T : Set G) :=
    (Subgroup.closure_le _).2 fun x hx => (mem_inf.1 hx.1).2
  have hTe : T ≤ centralizer ({(e : G)} : Set G) := fun t ht =>
    mem_centralizer_singleton_iff.2 ((mem_centralizer_iff.1 (hZC hS.mem) t ht))
  have hTK : T ≤ normalizer (Kv hyp e : Set G) := by
    have h1 : T ≤ normalizer ((L ⊓ centralizer ({(e : G)} : Set G) : Subgroup G) : Set G) :=
      fun t ht => A4.mem_normalizer_inf (hyp.normalizes ht) (le_normalizer (hTe ht))
    exact (h1.trans (normalizer_le_normalizer_oTwoUpper _)).trans
      (normalizer_le_normalizer_perfectCore _)
  have hJT : thompsonJ T ≤ T := iSup₂_le fun _ hA => hA.1
  have hJK : ⁅Kv hyp e, thompsonJ T⁆ ≤ Kv hyp e :=
    (le_normalizer_iff_commutator_le_left).1 (hJT.trans hTK)
  suffices hsuff : ∃ A, IsMaxElemAbelian T A ∧ ¬ ⁅Kv hyp e, A⁆ ≤ centralizer (V : Set G) by
    obtain ⟨A₁, hA₁, hKA⟩ := hsuff
    refine le_antisymm ?_ hJK
    calc Kv hyp e = ⁅Kv hyp e, A₁⁆ :=
          Kv_eq_commutator_of_not_le hyp h he (hA₁.1.trans hTK) hKA
      _ ≤ ⁅Kv hyp e, thompsonJ T⁆ :=
          commutator_mono le_rfl (le_iSup₂_of_le A₁ hA₁ le_rfl)
  have hLJ : L = ⁅L, thompsonJ T⁆ := (h1229 G T L V hyp).2 hS.cz
  obtain ⟨A, hAmax, hAV⟩ : ∃ A, IsMaxElemAbelian T A ∧ ¬ A ≤ centralizer (V : Set G) := by
    by_contra hcon
    push Not at hcon
    have hJV : thompsonJ T ≤ centralizer (V : Set G) := iSup₂_le fun A hA => hcon A hA
    have hLC : L ≤ centralizer (V : Set G) := by
      rw [hLJ, commutator_le]
      intro l hl j hj
      have hjv := mem_centralizer_iff.1 (hJV hj)
      have hconj : l * j * l⁻¹ ∈ centralizer (V : Set G) := by
        rw [mem_centralizer_iff]
        intro w hw
        have hw' : l⁻¹ * w * l⁻¹⁻¹ ∈ V := (mem_normalizer_iff.1 (hLV (inv_mem hl)) w).1 hw
        rw [inv_inv] at hw'
        have h1 := hjv _ hw'
        calc w * (l * j * l⁻¹) = l * ((l⁻¹ * w * l) * j) * l⁻¹ := by group
          _ = l * (j * (l⁻¹ * w * l)) * l⁻¹ := by rw [h1]
          _ = l * j * l⁻¹ * w := by group
      have := (centralizer (V : Set G)).mul_mem hconj
        ((centralizer (V : Set G)).inv_mem (hJV hj))
      rw [commutatorElement_def]
      exact this
    apply hyp.irrPlus.2.1
    rw [← hyp.irrPlus.2.2.2.1, eq_bot_iff, commutator_le]
    intro v hv l hl
    rw [mem_bot, commutatorElement_def, mem_centralizer_iff.1 (hLC hl) v hv]
    group
  by_cases hcase : ⁅Kv hyp e, A⁆ ≤ centralizer (V : Set G)
  swap
  · exact ⟨A, hAmax, hcase⟩
  set ρ := coordRep ψ (le_refl (normalizer (V : Set G))) h.Nact with hρdef
  have hρL : ∀ l : L, ρ ⟨l, hLV l.2⟩ = (natLam h.L_le h.Lact l : Perm (Fin 7)) := fun l =>
    IsCoordAct.unique ψ (hLV l.2) (coordRep_spec ψ le_rfl h.Nact ⟨l, hLV l.2⟩)
      (natLam_spec h.L_le h.Lact l)
  have hρ1 : ∀ x : normalizer (V : Set G), ρ x = 1 ↔ (x : G) ∈ centralizer (V : Set G) :=
    fun x => coordRep_eq_one_iff ψ le_rfl h.Nact x
  have hρe : ∀ x : normalizer (V : Set G),
      permAct7 (ρ x) vecFS = vecFS → (x : G) ∈ centralizer ({(e : G)} : Set G) := by
    intro x hx
    have hspec := coordRep_spec ψ le_rfl h.Nact x
    let y : V := ⟨(x : G) * e * (x : G)⁻¹, (mem_normalizer_iff.1 x.2 e).1 e.2⟩
    have hy : vec ψ y = vec ψ e := by
      rw [hspec e y rfl, he]
      exact hx
    have hye : (x : G) * e * (x : G)⁻¹ = e := congrArg Subtype.val (vec_injective ψ hy)
    rw [mem_centralizer_singleton_iff]
    calc (x : G) * e = (x : G) * e * (x : G)⁻¹ * x := by group
      _ = e * x := by rw [hye]
  have hρe' : ∀ x : normalizer (V : Set G),
      (x : G) ∈ centralizer ({(e : G)} : Set G) → permAct7 (ρ x) vecFS = vecFS := by
    intro x hx
    have hspec := coordRep_spec ψ le_rfl h.Nact x
    have hxe : (x : G) * e * (x : G)⁻¹ = e := by
      rw [mem_centralizer_singleton_iff.1 hx, mul_inv_cancel_right]
    have h1 := hspec e e hxe.symm
    rw [he] at h1
    exact h1.symm
  have hcomm : ∀ B : Subgroup G, B ≤ T → ⁅Kv hyp e, B⁆ ≤ centralizer (V : Set G) →
      ∀ (b : G) (hbN : b ∈ normalizer (V : Set G)), b ∈ B → ∀ τ ∈ altFive,
        ρ ⟨b, hbN⟩ * (τ : Perm (Fin 7)) = τ * ρ ⟨b, hbN⟩ := by
    intro B hBT hBV b hbN hb τ hτ
    obtain ⟨k, hkK, hk⟩ := exists_mem_Kv_natLam hyp h he hτ
    have hkb : (k : G) * b * (k : G)⁻¹ * b⁻¹ ∈ centralizer (V : Set G) := by
      have := hBV (commutator_mem_commutator hkK hb)
      rwa [commutatorElement_def] at this
    have h1 : ρ (⟨k, hLV k.2⟩ * ⟨b, hbN⟩ * (⟨k, hLV k.2⟩ : normalizer (V : Set G))⁻¹ *
        (⟨b, hbN⟩ : normalizer (V : Set G))⁻¹) = 1 := (hρ1 _).2 hkb
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hρL k, hk] at h1
    have h2 : (τ : Perm (Fin 7)) * ρ ⟨b, hbN⟩ * (τ : Perm (Fin 7))⁻¹ = ρ ⟨b, hbN⟩ := by
      have := mul_eq_one_iff_eq_inv.1 h1
      rwa [inv_inv] at this
    calc ρ ⟨b, hbN⟩ * (τ : Perm (Fin 7))
        = (τ : Perm (Fin 7)) * ρ ⟨b, hbN⟩ * (τ : Perm (Fin 7))⁻¹ * τ := by rw [h2]
      _ = τ * ρ ⟨b, hbN⟩ := by group
  have hA56 : ∀ (a : G) (haN : a ∈ normalizer (V : Set G)), a ∈ A →
      ρ ⟨a, haN⟩ = 1 ∨ ρ ⟨a, haN⟩ = swap 5 6 := by
    intro a haN ha
    have hc := hcomm A hAmax.1 hcase a haN ha
    exact perm_eq_one_or_swap_of_commute (hc _ a5cyc012_mem) (hc _ a5cyc123_mem)
      (hc _ a5cyc234_mem)
  obtain ⟨a₀, ha₀A, ha₀V⟩ : ∃ a ∈ A, a ∉ centralizer (V : Set G) := by
    by_contra hcon
    push Not at hcon
    exact hAV hcon
  have ha₀N : a₀ ∈ normalizer (V : Set G) := hTV (hAmax.1 ha₀A)
  have hρa₀ : ρ ⟨a₀, ha₀N⟩ = swap 5 6 := by
    rcases hA56 a₀ ha₀N ha₀A with h1 | h1
    · exact absurd ((hρ1 _).1 h1) ha₀V
    · exact h1
  obtain ⟨x, hxL, hx⟩ := h.Lonto (dbl0516 : Perm (Fin 7)) dbl0516.2
  have hxN : x ∈ normalizer (V : Set G) := hLV hxL
  have hρx : ρ ⟨x, hxN⟩ = dbl0516 :=
    IsCoordAct.unique ψ hxN (coordRep_spec ψ le_rfl h.Nact ⟨x, hxN⟩) hx
  have hYC : A.map (MulAut.conj x).toMonoidHom ≤
      centralizer ({(e : G)} : Set G) ⊓ normalizer (V : Set G) := by
    rintro _ ⟨a, ha, rfl⟩
    change x * a * x⁻¹ ∈ centralizer ({(e : G)} : Set G) ⊓ normalizer (V : Set G)
    have haN : a ∈ normalizer (V : Set G) := hTV (hAmax.1 ha)
    have hyN : x * a * x⁻¹ ∈ normalizer (V : Set G) :=
      (normalizer (V : Set G)).mul_mem ((normalizer (V : Set G)).mul_mem hxN haN)
        ((normalizer (V : Set G)).inv_mem hxN)
    refine ⟨?_, hyN⟩
    have hρy : ρ ⟨x * a * x⁻¹, hyN⟩ =
        (dbl0516 : Perm (Fin 7)) * ρ ⟨a, haN⟩ * (dbl0516 : Perm (Fin 7))⁻¹ := by
      have : (⟨x * a * x⁻¹, hyN⟩ : normalizer (V : Set G)) =
          ⟨x, hxN⟩ * ⟨a, haN⟩ * (⟨x, hxN⟩ : normalizer (V : Set G))⁻¹ := rfl
      rw [this, map_mul, map_mul, map_inv, hρx]
    apply hρe ⟨x * a * x⁻¹, hyN⟩
    rw [hρy]
    rcases hA56 a haN ha with h1 | h1
    · rw [h1, mul_one, mul_inv_cancel]
      decide
    · rw [h1, dbl0516_conj_swap]
      decide
  have hTC : T ≤ centralizer ({(e : G)} : Set G) ⊓ normalizer (V : Set G) := le_inf hTe hTV
  have hTsyl : QuasithinUnique.IsSylowTwoOf T
      (centralizer ({(e : G)} : Set G) ⊓ normalizer (V : Set G)) :=
    isSylowTwoOf_of_le hyp.sylow hTC
  have hYel := isElemAbelian_map_conj hAmax.2.1 x
  have hY2 : IsPGroup 2 (A.map (MulAut.conj x).toMonoidHom) := fun y =>
    ⟨1, Subtype.ext (by
      simp only [pow_one, SubmonoidClass.coe_pow, OneMemClass.coe_one]
      exact hYel.2 y y.2)⟩
  obtain ⟨S', hYS', hS'⟩ := QuasithinUnique.exists_isSylowTwoOf_of_le hYC hY2
  obtain ⟨c, hcC, hS'eq⟩ := hTsyl.exists_conj hS'
  have hcN : c ∈ normalizer (V : Set G) := hcC.2
  have hA₁T : A.map (MulAut.conj (c⁻¹ * x)).toMonoidHom ≤ T := by
    rintro _ ⟨a, ha, rfl⟩
    have hy : x * a * x⁻¹ ∈ S' := hYS' ⟨a, ha, rfl⟩
    rw [hS'eq] at hy
    obtain ⟨t, ht, hty⟩ := hy
    have hty' : c * t * c⁻¹ = x * a * x⁻¹ := hty
    change (c⁻¹ * x) * a * (c⁻¹ * x)⁻¹ ∈ T
    have : (c⁻¹ * x) * a * (c⁻¹ * x)⁻¹ = t := by
      calc (c⁻¹ * x) * a * (c⁻¹ * x)⁻¹ = c⁻¹ * (x * a * x⁻¹) * c := by group
        _ = c⁻¹ * (c * t * c⁻¹) * c := by rw [hty']
        _ = t := by group
    rw [this]
    exact ht
  have hA₁max : IsMaxElemAbelian T (A.map (MulAut.conj (c⁻¹ * x)).toMonoidHom) := by
    refine ⟨hA₁T, isElemAbelian_map_conj hAmax.2.1 _, fun B hBT hB => ?_⟩
    rw [Subgroup.card_map_of_injective (MulAut.conj (c⁻¹ * x)).injective]
    exact hAmax.2.2 B hBT hB
  refine ⟨_, hA₁max, fun hcon => ?_⟩
  have ha₁A : (c⁻¹ * x) * a₀ * (c⁻¹ * x)⁻¹ ∈ A.map (MulAut.conj (c⁻¹ * x)).toMonoidHom :=
    ⟨a₀, ha₀A, rfl⟩
  have ha₁N : (c⁻¹ * x) * a₀ * (c⁻¹ * x)⁻¹ ∈ normalizer (V : Set G) := hTV (hA₁T ha₁A)
  have hρa₁ : ρ ⟨(c⁻¹ * x) * a₀ * (c⁻¹ * x)⁻¹, ha₁N⟩ =
      (ρ ⟨c, hcN⟩)⁻¹ * swap 0 1 * ρ ⟨c, hcN⟩ := by
    have : (⟨(c⁻¹ * x) * a₀ * (c⁻¹ * x)⁻¹, ha₁N⟩ : normalizer (V : Set G)) =
        ((⟨c, hcN⟩ : normalizer (V : Set G))⁻¹ * ⟨x, hxN⟩) * ⟨a₀, ha₀N⟩ *
          ((⟨c, hcN⟩ : normalizer (V : Set G))⁻¹ * ⟨x, hxN⟩)⁻¹ := rfl
    rw [this, map_mul, map_mul, map_inv, map_mul, map_inv, hρx, hρa₀, ← dbl0516_conj_swap]
    group
  have hce : permAct7 (ρ ⟨c, hcN⟩) vecFS = vecFS := hρe' ⟨c, hcN⟩ hcC.1
  have h56 := (permAct7_vecFS_iff _).1 hce
  have hpq : (ρ ⟨c, hcN⟩)⁻¹ 0 ≠ (ρ ⟨c, hcN⟩)⁻¹ 1 := fun h' =>
    absurd ((ρ ⟨c, hcN⟩)⁻¹.injective h') (by decide)
  have hout : ∀ i : Fin 7, (i : ℕ) < 5 → ((ρ ⟨c, hcN⟩)⁻¹ i : ℕ) < 5 := by
    intro i hi
    have hlt := ((ρ ⟨c, hcN⟩)⁻¹ i).isLt
    by_contra hge
    push Not at hge
    have hv : ∀ j : Fin 7, 5 ≤ (j : ℕ) → j = 5 ∨ j = 6 := by decide
    have hπi : ρ ⟨c, hcN⟩ ((ρ ⟨c, hcN⟩)⁻¹ i) = i := Equiv.Perm.eq_inv_iff_eq.1 rfl
    rcases hv _ hge with h5 | h6
    · rw [h5] at hπi
      rcases h56 with ⟨h5', -⟩ | ⟨h5', -⟩ <;> rw [h5'] at hπi <;> rw [← hπi] at hi <;>
        exact absurd hi (by decide)
    · rw [h6] at hπi
      rcases h56 with ⟨-, h6'⟩ | ⟨-, h6'⟩ <;> rw [h6'] at hπi <;> rw [← hπi] at hi <;>
        exact absurd hi (by decide)
  have hswap : ρ ⟨(c⁻¹ * x) * a₀ * (c⁻¹ * x)⁻¹, ha₁N⟩ =
      swap ((ρ ⟨c, hcN⟩)⁻¹ 0) ((ρ ⟨c, hcN⟩)⁻¹ 1) := by
    rw [hρa₁, swap_apply_apply, inv_inv]
  have hc := hcomm _ hA₁T hcon _ ha₁N ha₁A
  apply not_commute_swap_of_lt_five _ _ hpq (hout 0 (by decide)) (hout 1 (by decide))
  rw [← hswap]
  exact ⟨hc _ a5cyc012_mem, hc _ a5cyc123_mem, hc _ a5cyc234_mem⟩

end CFSG.Quasithin.H13.A7
