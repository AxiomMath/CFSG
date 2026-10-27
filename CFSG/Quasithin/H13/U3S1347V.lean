module

public import CFSG.Quasithin.H13.U3S1347U
public import CFSG.Quasithin.H13.NQS134Defs
public import CFSG.Quasithin.H13.U3S1347O
public import CFSG.Quasithin.H13.U3S1347R
public import CFSG.Quasithin.H13.U3S1347T

public section

namespace CFSG.Quasithin.H13.U3

open Subgroup Equiv CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.H13.A6 CFSG.LieType.BorelTits
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

theorem s1347_A6_I (h1345 : NQS134.Stmt13_4_5) (S : A6.Setting134 G T L V) {H₁ H₂ : Subgroup G}
    (hH₀ : InH T (H₁ ⊔ H₂)) (hH₀M : ¬ H₁ ⊔ H₂ ≤ normalizer (L : Set G))
    (hns : ¬ Group.IsSolvable ↥(H₁ ⊔ H₂)) (hZinf : cZ T H₁ ⊓ cZ T H₂ = ⊥) {K₀ : Subgroup G}
    (hK₀ : K₀ ∈ cComp (H₁ ⊔ H₂))
    (hA6 : Nonempty (↥K₀ ⧸ CFSG.pCore 2 ↥K₀ ≃* alternatingGroup (Fin 6)))
    (hsup : H₁ ⊔ H₂ = K₀ ⊔ T)
    (hcentK : K₀ ⊓ centralizer (v0Of T H₁ H₂ : Set G) = pCoreOf 2 K₀) :
    ∃ I : Subgroup G, ∃ _ : IsMulCommutative ↥I, I ≤ v0Of T H₁ H₂ ∧
      H₁ ⊔ H₂ ≤ normalizer (I : Set G) ∧ ¬ K₀ ≤ centralizer (I : Set G) ∧
      (∀ J : Subgroup G, J ≤ I → K₀ ≤ normalizer (J : Set G) → J = ⊥ ∨ J = I) ∧
      AlternatingNatural (V := ↥I) (autOn K₀ I) ⊤ ⊥ 6 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hall⟩ := h1345 G T L V S (H₁ ⊔ H₂) hH₀ hH₀M hns
  obtain ⟨-, hN, -, -, -, -, -, ⟨I, hI⟩, hIall⟩ := hall K₀ hK₀
  obtain ⟨hTI, -, hIgen, ⟨hIc, hIcases⟩, -, -⟩ := hIall I hI
  obtain ⟨-, hIne, hKI, hIK, -, hIirr, -⟩ := hI
  have hKH := le_of_mem_cComp hK₀
  have hred := s1347_reduced S hH₀
  have hIV : I ≤ v0Of T H₁ H₂ := by
    have h1 : conjClosure (quasithinOmegaOneCenter T ⊓ I) K₀ ≤ v0Of T H₁ H₂ :=
      conjClosure_mono inf_le_left hKH
    rw [← hIgen] at h1
    exact h1
  have hH₀I : H₁ ⊔ H₂ ≤ normalizer (I : Set G) := hsup ▸ sup_le hKI hTI
  have hKIc : ¬ K₀ ≤ centralizer (I : Set G) := fun hle => hIne (by
    rw [← hIK]
    exact commutator_eq_bot_iff_le_centralizer.2 (le_centralizer_iff.1 hle))
  have hs := (simple_of_cases (Or.inr (Or.inr hA6))).1
  have hO : pCoreOf 2 K₀ ≤ centralizer (I : Set G) :=
    (hcentK ▸ inf_le_right : pCoreOf 2 K₀ ≤ centralizer (v0Of T H₁ H₂ : Set G)).trans
      (centralizer_le (SetLike.coe_subset_coe.2 hIV))
  have hKC : K₀ ⊓ centralizer (I : Set G) = pCoreOf 2 K₀ := by
    refine le_antisymm (le_pCoreOf_of_normal inf_le_left (fun k hk => mem_normalizer_inf_of
      (le_normalizer hk) (mem_normalizer_centralizer_of_mem (hKI hk))) hs fun hle => ?_)
      (le_inf (pCoreOf_le 2 K₀) hO)
    exact hKIc (hle.trans (sup_le inf_le_right hO))
  have hcardK : Nat.card (↥K₀ ⧸ CFSG.pCore 2 ↥K₀) = 360 := by
    obtain ⟨e⟩ := hA6
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
      Fintype.card_fin]
    decide
  have hcardA : Nat.card (autOn K₀ I) = 360 := by
    rw [card_autOn_eq_relIndex hKI, hKC, ← hcardK, relIndex, pCoreOf_subgroupOf_eq_pCore]
    rfl
  rcases hIcases with ⟨h5, -⟩ | ⟨h6, hb⟩ | ⟨-, h2, -⟩ | ⟨hLie, -⟩
  ·
    exfalso
    obtain ⟨π, hπ, -⟩ := h5
    have hd : Nat.card (autOn K₀ I) ∣ Nat.card ↥(alternatingGroup (Fin 5)) :=
      card_dvd_of_surjective π hπ
    rw [hcardA, nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin] at hd
    exact absurd hd (by decide)
  · exact ⟨I, hIc, hIV, hH₀I, hKIc, fun J hJ hJK => by
      have := hIirr J (by rw [hb]; exact bot_le) hJ hJK
      rwa [hb] at this, h6⟩
  ·
    exfalso
    obtain ⟨z, hz, hz1⟩ := exists_ne_one_of_card_two h2
    have hTN : T ≤ normalizer (K₀ : Set G) := (hsup ▸ le_sup_right : T ≤ H₁ ⊔ H₂).trans hN
    have hzV := hIV (mem_inf.1 hz).1
    have hzT : ∀ t ∈ T, t * z = z * t := by
      intro t ht
      have htz : t * z * t⁻¹ ∈ I ⊓ centralizer (K₀ : Set G) :=
        (mem_normalizer_iff.1 (mem_normalizer_inf_of (hTI ht)
          (mem_normalizer_centralizer_of_mem (hTN ht))) z).1 hz
      rcases eq_one_or_eq_of_card_two h2 hz hz1 htz with h1 | h1
      · exfalso
        apply hz1
        calc z = t⁻¹ * (t * z * t⁻¹) * t := by group
          _ = 1 := by rw [h1]; group
      · calc t * z = t * z * t⁻¹ * t := by group
          _ = z * t := by rw [h1]
    have hzZ : z ∈ quasithinOmegaOneCenter T :=
      subset_closure ⟨⟨s1347_V0_le_T S hH₀ hzV, mem_centralizer_iff.2 hzT⟩, hred.2.2.1.2 z hzV⟩
    have hzC : ∀ g ∈ H₁ ⊔ H₂, g * z = z * g := by
      intro g hg
      rw [hsup] at hg
      obtain ⟨k, hk, t, ht, rfl⟩ := (B19Aux.mem_sup_iff_of_le_normalizer hTN).1 hg
      have hkz : k * z = z * k := mem_centralizer_iff.1 (mem_inf.1 hz).2 k hk
      calc k * t * z = k * (t * z) := by group
        _ = k * (z * t) := by rw [hzT t ht]
        _ = k * z * t := by group
        _ = z * k * t := by rw [hkz]
        _ = z * (k * t) := by group
    have hzH : z ∈ cZ T H₁ ⊓ cZ T H₂ :=
      mem_inf.2 ⟨mem_inf.2 ⟨hzZ, mem_centralizer_iff.2 fun g hg => hzC g (mem_sup_left hg)⟩,
        mem_inf.2 ⟨hzZ, mem_centralizer_iff.2 fun g hg => hzC g (mem_sup_right hg)⟩⟩
    rw [hZinf, mem_bot] at hzH
    exact hz1 hzH
  ·
    exfalso
    obtain ⟨e⟩ := nonempty_equiv_SL32_of_lieModel hLie
    have := Nat.card_congr e.toEquiv
    rw [hcardK, HSType.card_SL_three_two] at this
    norm_num at this

@[expose] def duadList : List (Perm (Fin 6)) :=
  [swap 4 0 * swap 5 1, swap 4 0 * swap 5 2, swap 4 0 * swap 5 3, swap 5 0 * swap 1 2,
    swap 4 0 * swap 1 2, swap 4 1 * swap 5 2, swap 4 1 * swap 5 3, swap 5 1 * swap 0 2,
    swap 4 1 * swap 0 2, swap 4 2 * swap 5 3, swap 5 2 * swap 0 1, swap 4 2 * swap 0 1,
    swap 5 3 * swap 0 1, swap 4 3 * swap 0 1, 1]

theorem duadList_sign : ∀ σ ∈ duadList, Perm.sign σ = 1 := by
  decide +kernel

theorem duadList_mem {σ : Perm (Fin 6)} (hσ : σ ∈ duadList) : σ ∈ alternatingGroup (Fin 6) :=
  Perm.mem_alternatingGroup.2 (duadList_sign σ hσ)

theorem orbit_dv45 : ∀ w : P6, InW4 w → w = 1 ∨ ∃ σ ∈ duadList, act4f σ (dv 4 5) = w := by
  decide +kernel

omit [Finite G] in
theorem le_normalizer_closure_conj {K H : Subgroup G} {y : G}
    (hcl : ∀ g ∈ H, ∀ k : ↥K, ∃ k' : ↥K, g * k * y * (g * k)⁻¹ = (k' : G) * y * (k' : G)⁻¹) :
    H ≤ normalizer ((closure (Set.range fun k : ↥K => (k : G) * y * (k : G)⁻¹) :
      Subgroup G) : Set G) := by
  have key : ∀ g ∈ H, ∀ n ∈ closure (Set.range fun k : ↥K => (k : G) * y * (k : G)⁻¹),
      g * n * g⁻¹ ∈ closure (Set.range fun k : ↥K => (k : G) * y * (k : G)⁻¹) := by
    intro g hg n hn
    induction hn using closure_induction with
    | mem n hn =>
      obtain ⟨k, rfl⟩ := hn
      obtain ⟨k', hk'⟩ := hcl g hg k
      have e : g * ((k : G) * y * (k : G)⁻¹) * g⁻¹ = g * k * y * (g * k)⁻¹ := by group
      rw [e, hk']
      exact subset_closure ⟨k', rfl⟩
    | one => simp
    | mul a b _ _ ha hb =>
      have e : g * (a * b) * g⁻¹ = g * a * g⁻¹ * (g * b * g⁻¹) := by group
      rw [e]
      exact mul_mem ha hb
    | inv a _ ha =>
      have e : g * a⁻¹ * g⁻¹ = (g * a * g⁻¹)⁻¹ := by group
      rw [e]
      exact inv_mem ha
  intro g hg
  rw [mem_normalizer_iff]
  intro n
  refine ⟨key g hg n, fun h => ?_⟩
  have := key g⁻¹ (inv_mem hg) _ h
  rwa [show g⁻¹ * (g * n * g⁻¹) * g⁻¹⁻¹ = n by group] at this

theorem s1347_A6_top (S : A6.Setting134 G T L V) {H₁ H₂ : Subgroup G}
    (hH₀ : InH T (H₁ ⊔ H₂)) {K₀ I : Subgroup G} [IsMulCommutative ↥I]
    (hKH : K₀ ≤ H₁ ⊔ H₂) (hN : H₁ ⊔ H₂ ≤ normalizer (K₀ : Set G)) (hsup : H₁ ⊔ H₂ = K₀ ⊔ T)
    (hIV : I ≤ v0Of T H₁ H₂) (hH₀I : H₁ ⊔ H₂ ≤ normalizer (I : Set G))
    (hIirr : ∀ J : Subgroup G, J ≤ I → K₀ ≤ normalizer (J : Set G) → J = ⊥ ∨ J = I)
    {ρ : ↥(H₁ ⊔ H₂) →* Perm (Fin 6)} {ψ : ↥I ≃* ↥W4}
    (hψ : ∀ (h : ↥(H₁ ⊔ H₂)) (v : ↥I), ψ (conjAct I ⟨h, hH₀I h.2⟩ v) = act4 (ρ h) (ψ v))
    (hTH : T ≤ H₁ ⊔ H₂) (hρT : ∀ t (ht : t ∈ T), InD6 (ρ ⟨t, hTH ht⟩))
    (hρK : ∀ σ : Perm (Fin 6), (∃ k, ∃ hk : k ∈ K₀, ρ ⟨k, hKH hk⟩ = σ) ↔
      σ ∈ alternatingGroup (Fin 6))
    (hker : ∀ h : ↥(H₁ ⊔ H₂), ρ h = 1 ↔ (h : G) ∈ centralizer (v0Of T H₁ H₂ : Set G))
    {Hp Hl : Subgroup G} (hHp : Hp ≤ H₁ ⊔ H₂)
    (hP : (Hp.subgroupOf (H₁ ⊔ H₂)).map ρ =
      (P1sub ⊓ alternatingGroup (Fin 6)) ⊔ (T.subgroupOf (H₁ ⊔ H₂)).map ρ)
    (hL : (Hl.subgroupOf (H₁ ⊔ H₂)).map ρ =
      (P2sub ⊓ alternatingGroup (Fin 6)) ⊔ (T.subgroupOf (H₁ ⊔ H₂)).map ρ)
    {x y : G} (hx : x ∈ cZ T Hp) (hy : y ∈ cZ T Hl) (hyp : y ∉ centralizer (Hp : Set G))
    (hZ : ∀ z ∈ quasithinOmegaOneCenter T, z = 1 ∨ z = x ∨ z = y ∨ z = x * y) :
    ∃ F₀ : ↥(v0Of T H₁ H₂) →* ↥W4, Function.Surjective F₀ ∧
      (∀ v : ↥(v0Of T H₁ H₂), (v : G) ∈ I → F₀ v = 1) ∧
      (∀ t (ht : t ∈ T) (v : ↥(v0Of T H₁ H₂)) (hv : t * v * t⁻¹ ∈ v0Of T H₁ H₂),
        F₀ ⟨t * v * t⁻¹, hv⟩ = act4 (S6Out.phiEquiv.symm (ρ ⟨t, hTH ht⟩)) (F₀ v)) ∧
      (∀ k (hk : k ∈ K₀) (v : ↥(v0Of T H₁ H₂)) (hv : k * v * k⁻¹ ∈ v0Of T H₁ H₂),
        F₀ ⟨k * v * k⁻¹, hv⟩ = act4 (S6Out.phiEquiv.symm (ρ ⟨k, hKH hk⟩)) (F₀ v)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hred := s1347_reduced S hH₀
  have hV₀ : IsElemAbelian 2 (v0Of T H₁ H₂) := hred.2.2.1
  have : IsMulCommutative ↥(v0Of T H₁ H₂) := hV₀.1
  have hV₀T := s1347_V0_le_T S hH₀
  have hV₀N : H₁ ⊔ H₂ ≤ normalizer (v0Of T H₁ H₂ : Set G) := hred.2.1
  have hTN : T ≤ normalizer (K₀ : Set G) := hTH.trans hN
  have hZT : ∀ z ∈ quasithinOmegaOneCenter T, ∀ t ∈ T, t * z = z * t := fun z hz t ht =>
    mem_centralizer_iff.1 (s134_Z_le_center T hz).2 t ht
  have hD1 : ∀ σ, InD6 σ → InP1 σ := fun σ h => ⟨h.1, h.2.1⟩
  have hHpP1 : ∀ h : ↥(H₁ ⊔ H₂), (h : G) ∈ Hp → InP1 (ρ h) := by
    intro h hh
    have hm : ρ h ∈ (Hp.subgroupOf (H₁ ⊔ H₂)).map ρ := mem_map_of_mem _ (mem_subgroupOf.2 hh)
    rw [hP] at hm
    refine (sup_le inf_le_left ?_ : _ ≤ P1sub) hm
    rintro _ ⟨t, ht, rfl⟩
    exact hD1 _ (hρT t (mem_subgroupOf.1 ht))
  set w₀ : ↥I := ψ.symm ⟨dv 4 5, dv_mem 4 5⟩ with hw₀
  have hψw₀ : ψ w₀ = ⟨dv 4 5, dv_mem 4 5⟩ := ψ.apply_symm_apply _
  have hw₀fix : ∀ h : ↥(H₁ ⊔ H₂), InP1 (ρ h) → (h : G) * w₀ * (h : G)⁻¹ = w₀ := by
    intro h hh
    have h1 : ψ (conjAct I ⟨h, hH₀I h.2⟩ w₀) = ψ w₀ := by
      rw [hψ, hψw₀]
      exact Subtype.ext ((fix_dv45_iff _).2 hh)
    rw [← conjAct_val (hH₀I h.2), ψ.injective h1]
  have hw₀Z : (w₀ : G) ∈ quasithinOmegaOneCenter T := by
    refine subset_closure ⟨⟨hV₀T (hIV w₀.2), mem_centralizer_iff.2 fun t ht => ?_⟩,
      hV₀.2 _ (hIV w₀.2)⟩
    have h1 := hw₀fix ⟨t, hTH ht⟩ (hD1 _ (hρT t ht))
    calc t * (w₀ : G) = t * w₀ * t⁻¹ * t := by group
      _ = w₀ * t := by rw [h1]
  have hw₀p : (w₀ : G) ∈ centralizer (Hp : Set G) := mem_centralizer_iff.2 fun h hh => by
    have h1 := hw₀fix ⟨h, hHp hh⟩ (hHpP1 ⟨h, hHp hh⟩ hh)
    calc h * (w₀ : G) = h * w₀ * h⁻¹ * h := by group
      _ = w₀ * h := by rw [h1]
  have hw₀1 : (w₀ : G) ≠ 1 := by
    intro h1
    have h2 : w₀ = 1 := Subtype.ext h1
    rw [h2, map_one] at hψw₀
    exact VolI.G53.dv45_ne_one (congrArg Subtype.val hψw₀).symm
  have hxp : x ∈ centralizer (Hp : Set G) := (mem_inf.1 hx).2
  have hw₀x : (w₀ : G) = x := by
    rcases hZ _ hw₀Z with h1 | h1 | h1 | h1
    · exact absurd h1 hw₀1
    · exact h1
    · exact absurd (h1 ▸ hw₀p) hyp
    · exfalso
      apply hyp
      have e : y = x⁻¹ * (w₀ : G) := by rw [h1]; group
      rw [e]
      exact mul_mem (inv_mem hxp) hw₀p
  have hxI : x ∈ I := hw₀x ▸ w₀.2
  have hyZ : y ∈ quasithinOmegaOneCenter T := (mem_inf.1 hy).1
  have hyV : y ∈ v0Of T H₁ H₂ := s1347_Z_le_V0 hyZ
  set Vy : Subgroup G := closure (Set.range fun k : ↥K₀ => (k : G) * y * (k : G)⁻¹) with hVy
  have hVyV : Vy ≤ v0Of T H₁ H₂ := by
    rw [hVy, closure_le]
    rintro _ ⟨k, rfl⟩
    exact (mem_normalizer_iff.1 (hV₀N (hKH k.2)) y).1 hyV
  have hH₀Vy : H₁ ⊔ H₂ ≤ normalizer (Vy : Set G) := by
    refine le_normalizer_closure_conj fun g hg k => ?_
    have hgk : g * k ∈ K₀ ⊔ T := by
      rw [← hsup]
      exact mul_mem hg (hKH k.2)
    obtain ⟨k', hk', t, ht, he⟩ := (B19Aux.mem_sup_iff_of_le_normalizer hTN).1 hgk
    refine ⟨⟨k', hk'⟩, ?_⟩
    rw [he]
    have h1 := hZT y hyZ t ht
    show k' * t * y * (k' * t)⁻¹ = k' * y * k'⁻¹
    calc k' * t * y * (k' * t)⁻¹ = k' * (t * y) * t⁻¹ * k'⁻¹ := by group
      _ = k' * y * k'⁻¹ := by rw [h1]; group
  have : IsMulCommutative ↥Vy := ⟨⟨fun a b => Subtype.ext
    (congrArg (fun z : ↥(v0Of T H₁ H₂) => (z : G))
      (mul_comm (⟨a, hVyV a.2⟩ : ↥(v0Of T H₁ H₂)) ⟨b, hVyV b.2⟩))⟩⟩
  have hV2 : ∀ v ∈ Vy, v * v = 1 := fun v hv => by
    rw [← sq]
    exact hV₀.2 v (hVyV hv)
  have hKVy : K₀ ≤ normalizer (Vy : Set G) := hKH.trans hH₀Vy
  have hyVy : y ∈ Vy := by
    have h1 : ((1 : ↥K₀) : G) * y * ((1 : ↥K₀) : G)⁻¹ ∈ Vy := subset_closure ⟨1, rfl⟩
    simpa using h1
  let θ : ↥K₀ →* ↥(alternatingGroup (Fin 6)) :=
    (ρ.comp (inclusion hKH)).codRestrict _ fun k => (hρK _).1 ⟨k, k.2, rfl⟩
  have hθv : ∀ k : ↥K₀, ((θ k : ↥(alternatingGroup (Fin 6))) : Perm (Fin 6)) =
      ρ ⟨k, hKH k.2⟩ := fun _ => rfl
  have hθ : Function.Surjective θ := by
    intro σ
    obtain ⟨k, hk, hkσ⟩ := (hρK σ).2 σ.2
    exact ⟨⟨k, hk⟩, Subtype.ext hkσ⟩
  have hθker : ∀ k : ↥K₀, θ k = 1 → (k : G) ∈ centralizer (Vy : Set G) := by
    intro k hk
    have h1 : ρ ⟨k, hKH k.2⟩ = 1 := congrArg Subtype.val hk
    exact centralizer_le (SetLike.coe_subset_coe.2 hVyV) ((hker _).1 h1)
  have hfix : ∀ k : ↥K₀, (θ k : Perm (Fin 6)) ∈ P2sub → (k : G) * y = y * k := by
    intro k hk
    have hm : ρ ⟨k, hKH k.2⟩ ∈ (Hl.subgroupOf (H₁ ⊔ H₂)).map ρ := by
      rw [hL]
      exact mem_sup_left (mem_inf.2 ⟨hk, (θ k).2⟩)
    obtain ⟨h, hh, hhk⟩ := hm
    have h1 : ρ (h⁻¹ * ⟨k, hKH k.2⟩) = 1 := by rw [map_mul, map_inv, hhk, inv_mul_cancel]
    have hc : (h : G)⁻¹ * k ∈ centralizer (v0Of T H₁ H₂ : Set G) := (hker _).1 h1
    have hc1 : y * ((h : G)⁻¹ * k) = (h : G)⁻¹ * k * y := mem_centralizer_iff.1 hc y hyV
    have hc2 : (h : G) * y = y * h :=
      mem_centralizer_iff.1 (mem_inf.1 hy).2 h (mem_subgroupOf.1 hh)
    calc (k : G) * y = h * ((h : G)⁻¹ * k * y) := by group
      _ = h * (y * ((h : G)⁻¹ * k)) := by rw [hc1]
      _ = h * y * ((h : G)⁻¹ * k) := by group
      _ = y * h * ((h : G)⁻¹ * k) := by rw [hc2]
      _ = y * k := by group
  have hmove : ∃ k : ↥K₀, (k : G) * y ≠ y * k := by
    by_contra hcon'
    have hcon : ∀ k : ↥K₀, (k : G) * y = y * k := fun k => by
      by_contra hne
      exact hcon' ⟨k, hne⟩
    apply hyp
    refine mem_centralizer_iff.2 fun h hh => ?_
    have hh0 : h ∈ K₀ ⊔ T := hsup ▸ hHp hh
    obtain ⟨k, hk, t, ht, rfl⟩ := (B19Aux.mem_sup_iff_of_le_normalizer hTN).1 hh0
    have h1 := hcon ⟨k, hk⟩
    have h2 := hZT y hyZ t ht
    calc k * t * y = k * (t * y) := by group
      _ = k * (y * t) := by rw [h2]
      _ = k * y * t := by group
      _ = y * k * t := by rw [h1]
      _ = y * (k * t) := by group
  obtain ⟨F, hFs, hFe, hFy⟩ := exists_top_map hV2 hKVy θ hθ hθker hyVy hVy hfix hmove
  have hFT : ∀ t (ht : t ∈ T) (v : ↥Vy), F (conjAct Vy ⟨t, hH₀Vy (hTH ht)⟩ v) =
      act4 (S6Out.phiEquiv.symm (ρ ⟨t, hTH ht⟩)) (F v) := by
    intro t ht v
    refine top_map_conj hKVy θ hyVy hVy hFe hFy (hH₀Vy (hTH ht)) (hN (hTH ht))
      (hZT y hyZ t ht) (hρT t ht) (fun k => ?_) v
    show ρ ⟨t * k * t⁻¹, _⟩ = ρ ⟨t, hTH ht⟩ * ρ ⟨k, hKH k.2⟩ * (ρ ⟨t, hTH ht⟩)⁻¹
    rw [← map_inv, ← map_mul, ← map_mul]
    rfl
  have hKIVy : K₀ ≤ normalizer ((I ⊓ Vy : Subgroup G) : Set G) := fun k hk =>
    mem_normalizer_inf_of (hH₀I (hKH hk)) (hKVy hk)
  have hIF : ∀ v : ↥Vy, (v : G) ∈ I → F v = 1 := by
    rcases hIirr (I ⊓ Vy) inf_le_left hKIVy with hb | he
    · intro v hv
      have h1 : (v : G) ∈ I ⊓ Vy := mem_inf.2 ⟨hv, v.2⟩
      rw [hb, mem_bot] at h1
      have h2 : v = 1 := Subtype.ext h1
      rw [h2, map_one]
    · have hIVy : I ≤ Vy := he ▸ inf_le_right
      have key : ∀ σ : Perm (Fin 6), σ ∈ alternatingGroup (Fin 6) → InP1 σ →
          act4 (S6Out.phiEquiv.symm σ) (F ⟨w₀, hIVy w₀.2⟩) = F ⟨w₀, hIVy w₀.2⟩ := by
        intro σ hσA hσ
        obtain ⟨k, hk, hkσ⟩ := (hρK σ).2 hσA
        have h1 := hFe ⟨k, hk⟩ ⟨w₀, hIVy w₀.2⟩
        have h2 : conjAct Vy ⟨k, hKVy hk⟩ ⟨w₀, hIVy w₀.2⟩ = ⟨w₀, hIVy w₀.2⟩ := Subtype.ext (by
          rw [conjAct_val]
          exact hw₀fix ⟨k, hKH hk⟩ (hkσ ▸ hσ))
        have e : ((θ ⟨k, hk⟩ : ↥(alternatingGroup (Fin 6))) : Perm (Fin 6)) = σ := hkσ
        rw [e, h2] at h1
        exact h1.symm
      have hs1 := key (swap 2 3 * swap 4 5) (Perm.mem_alternatingGroup.2 (by decide))
        (by decide)
      have hs2 := key (swap 1 2 * swap 4 5) (Perm.mem_alternatingGroup.2 (by decide))
        (by decide)
      rw [S6Out.phi_inv_eq, phi_inv_P1_gens.1] at hs1
      rw [S6Out.phi_inv_eq, phi_inv_P1_gens.2] at hs2
      have hFw₀ : F ⟨w₀, hIVy w₀.2⟩ = 1 := Subtype.ext (fix_P1_gens_tw _ (F _).2
        (congrArg Subtype.val hs1) (congrArg Subtype.val hs2))
      intro v hv
      rcases orbit_dv45 (ψ ⟨v, hv⟩ : P6) (ψ ⟨v, hv⟩).2 with h1 | ⟨σ, hσ, hσv⟩
      · have h2 : (⟨v, hv⟩ : ↥I) = 1 := ψ.injective (by rw [map_one]; exact Subtype.ext h1)
        have h3 : v = 1 := Subtype.ext (congrArg (fun z : ↥I => (z : G)) h2)
        rw [h3, map_one]
      · obtain ⟨k, hk, hkσ⟩ := (hρK σ).2 (duadList_mem hσ)
        have h2 := hψ ⟨k, hKH hk⟩ w₀
        rw [hψw₀] at h2
        have h2' : ψ (conjAct I ⟨k, hH₀I (hKH hk)⟩ w₀) = ψ ⟨v, hv⟩ := by
          refine h2.trans (Subtype.ext ?_)
          rw [← hσv]
          show act4f (ρ ⟨k, hKH hk⟩) (dv 4 5) = act4f σ (dv 4 5)
          rw [hkσ]
        have h3 := ψ.injective h2'
        have hv' : (v : G) = k * w₀ * k⁻¹ := by
          rw [← conjAct_val (hH₀I (hKH hk)) w₀, h3]
        have e : v = conjAct Vy ⟨k, hKVy hk⟩ ⟨w₀, hIVy w₀.2⟩ :=
          Subtype.ext (by rw [conjAct_val]; exact hv')
        rw [e, hFe ⟨k, hk⟩, hFw₀, map_one]
  have hX : v0Of T H₁ H₂ ≤ I ⊔ Vy := by
    show conjClosure (quasithinOmegaOneCenter T) (H₁ ⊔ H₂) ≤ I ⊔ Vy
    refine conjClosure_le fun h hh z hz => ?_
    have hxc : h * x * h⁻¹ ∈ I ⊔ Vy := mem_sup_left ((mem_normalizer_iff.1 (hH₀I hh) x).1 hxI)
    have hyc : h * y * h⁻¹ ∈ I ⊔ Vy :=
      mem_sup_right ((mem_normalizer_iff.1 (hH₀Vy hh) y).1 hyVy)
    rcases hZ z hz with h1 | h1 | h1 | h1 <;> rw [h1]
    · rw [mul_one, mul_inv_cancel]
      exact one_mem _
    · exact hxc
    · exact hyc
    · have e : h * (x * y) * h⁻¹ = h * x * h⁻¹ * (h * y * h⁻¹) := by group
      rw [e]
      exact mul_mem hxc hyc
  obtain ⟨F₀, hF₀Y, hF₀I⟩ := exists_ext_of_sup hIV hVyV hX F hIF
  have hF₀s : Function.Surjective F₀ := fun w => by
    obtain ⟨v, hv⟩ := hFs w
    exact ⟨⟨v, hVyV v.2⟩, by rw [hF₀Y]; exact hv⟩
  have hF₀T : ∀ t (ht : t ∈ T) (v : ↥(v0Of T H₁ H₂)) (hv : t * v * t⁻¹ ∈ v0Of T H₁ H₂),
      F₀ ⟨t * v * t⁻¹, hv⟩ = act4 (S6Out.phiEquiv.symm (ρ ⟨t, hTH ht⟩)) (F₀ v) :=
    fun t ht v hv => ext_conj hIV hVyV hX hF₀Y hF₀I (hH₀I (hTH ht)) (hH₀Vy (hTH ht)) _
      (hFT t ht) v hv
  have hF₀K : ∀ k (hk : k ∈ K₀) (v : ↥(v0Of T H₁ H₂)) (hv : k * v * k⁻¹ ∈ v0Of T H₁ H₂),
      F₀ ⟨k * v * k⁻¹, hv⟩ = act4 (S6Out.phiEquiv.symm (ρ ⟨k, hKH hk⟩)) (F₀ v) :=
    fun k hk v hv => ext_conj hIV hVyV hX hF₀Y hF₀I (hH₀I (hKH hk)) (hKVy hk) _
      (hFe ⟨k, hk⟩) v hv
  exact ⟨F₀, hF₀s, hF₀I, hF₀T, hF₀K⟩

theorem s1347_A6_data (hedge : GoldschmidtEdgeBoundS3) (h1332 : Stmt13_3_2)
    (h1228 : Stmt12_2_8) (hC58 : TheoremC58) (h317 : AS317Sylow) (h56 : AsB56)
    (h135 : A6.Stmt13_3_5) (h1345 : NQS134.Stmt13_4_5) (S : A6.Setting134 G T L V)
    {H₁ H₂ : Subgroup G} (h : Hyp1347 T H₁ H₂) (hns : ¬ Group.IsSolvable ↥(H₁ ⊔ H₂))
    {K₀ : Subgroup G} (hK₀ : K₀ ∈ cComp (H₁ ⊔ H₂)) (hN : H₁ ⊔ H₂ ≤ normalizer (K₀ : Set G))
    (hA6 : Nonempty (↥K₀ ⧸ CFSG.pCore 2 ↥K₀ ≃* alternatingGroup (Fin 6)))
    (hK₁ : oTwoRes H₁ ≤ K₀) (hK₂ : oTwoRes H₂ ≤ K₀) (hsup : H₁ ⊔ H₂ = K₀ ⊔ T)
    (hcentK : K₀ ⊓ centralizer (v0Of T H₁ H₂ : Set G) = pCoreOf 2 K₀) :
    ∃ (I : Subgroup G) (_ : IsMulCommutative ↥I) (hH₀I : H₁ ⊔ H₂ ≤ normalizer (I : Set G))
      (ρ : ↥(H₁ ⊔ H₂) →* Perm (Fin 6)) (ψ : ↥I ≃* ↥W4) (F₀ : ↥(v0Of T H₁ H₂) →* ↥W4),
      I ≤ v0Of T H₁ H₂ ∧
      (∀ (g : ↥(H₁ ⊔ H₂)) (v : ↥I), ψ (conjAct I ⟨g, hH₀I g.2⟩ v) = act4 (ρ g) (ψ v)) ∧
      (∀ g : ↥(H₁ ⊔ H₂), (g : G) ∈ T → InD6 (ρ g)) ∧
      (∀ g : ↥(H₁ ⊔ H₂), (g : G) ∈ K₀ → ρ g ∈ alternatingGroup (Fin 6)) ∧
      (∀ g : ↥(H₁ ⊔ H₂), ρ g = 1 ↔ (g : G) ∈ centralizer (v0Of T H₁ H₂ : Set G)) ∧
      Function.Surjective F₀ ∧ (∀ v : ↥(v0Of T H₁ H₂), (v : G) ∈ I → F₀ v = 1) ∧
      ∀ (g : ↥(H₁ ⊔ H₂)) (v : ↥(v0Of T H₁ H₂)) (hv : (g : G) * v * (g : G)⁻¹ ∈ v0Of T H₁ H₂),
        (g : G) ∈ T ∨ (g : G) ∈ K₀ →
          F₀ ⟨g * v * (g : G)⁻¹, hv⟩ = act4 (S6Out.phiEquiv.symm (ρ g)) (F₀ v) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hH₀, hH₀M, -, hZsup, hZinf, hc₁, hc₂⟩ :=
    s1347_one_first hedge h1332 h1228 hC58 h317 h56 h135 S h
  have hKH := le_of_mem_cComp hK₀
  have hsyl₀ : IsSylowTwoOf T (H₁ ⊔ H₂) := A5.isSylowTwoOf_of_le S.h13.sylow hH₀.1
  have hTH : T ≤ H₁ ⊔ H₂ := hsyl₀.1
  have hT2 : IsPGroup 2 T := S.h13.sylow.1
  have hsylK : IsSylowTwoOf (T ⊓ K₀) K₀ := A4.isSylowTwoOf_inf_normal hsyl₀ hKH hN
  obtain ⟨I, hIc, hIV, hH₀I, hKI, hIirr, hAN⟩ :=
    s1347_A6_I h1345 S hH₀ hH₀M hns hZinf hK₀ hA6 hsup hcentK
  obtain ⟨ρ, ψ, hψ, hρT, hρD, hρK⟩ := s1347_A6_frame hKH hN hH₀I hTH hT2 hsylK hAN
  have hs := (simple_of_cases (Or.inr (Or.inr hA6))).1
  have hCI := s1347_inf_centralizer_I S hH₀ hKH hN hsup hs hcentK hIV hH₀I hKI
  have hkerV : ∀ g : ↥(H₁ ⊔ H₂), ρ g = 1 ↔ (g : G) ∈ centralizer (v0Of T H₁ H₂ : Set G) := by
    intro g
    rw [s1347_rho_eq_one_iff hH₀I hψ]
    exact ⟨fun hg => hCI (mem_inf.2 ⟨g.2, hg⟩),
      fun hg => centralizer_le (SetLike.coe_subset_coe.2 hIV) hg⟩
  have hcent₀ := s1347_centralizer_eq_A6 S h hH₀ hN hsup hcentK
  have hkerO : ∀ g : ↥(H₁ ⊔ H₂), ρ g = 1 ↔ (g : G) ∈ pCoreOf 2 (H₁ ⊔ H₂) := by
    intro g
    rw [hkerV, ← hcent₀]
    exact ⟨fun hg => mem_inf.2 ⟨g.2, hg⟩, fun hg => (mem_inf.1 hg).2⟩
  have hρK' : ∀ k (hk : k ∈ K₀), ρ ⟨k, hKH hk⟩ ∈ alternatingGroup (Fin 6) := fun k hk =>
    (hρK _).1 ⟨k, hk, rfl⟩
  have h3₁ := s1347_relIndex_three S h.inH₁.1 h.s3₁
  have h3₂ := s1347_relIndex_three S h.inH₂.1 h.s3₂
  have hO₂T : pCoreOf 2 (H₁ ⊔ H₂) ≤ T := pCoreOf_two_le_of_isSylowTwoOf hsyl₀
  have hnot : ∀ {Hi : Subgroup G}, T ≤ Hi → T.relIndex Hi = 3 →
      ¬ oTwoRes Hi ≤ pCoreOf 2 (H₁ ⊔ H₂) := by
    intro Hi hTi h3 hle
    have hsyl : IsSylowTwoOf T Hi := ⟨hTi, hT2, by
      show ¬ 2 ∣ T.relIndex Hi
      rw [h3]
      decide⟩
    have hHT : Hi ≤ T :=
      (le_oTwoRes_sup_of_isSylowTwoOf hsyl).trans (sup_le (hle.trans hO₂T) le_rfl)
    have h1 : T.relIndex Hi = 1 := relIndex_eq_one.2 hHT
    omega
  have hP₁ := s1347_A6_parabolic hT2 hTH hKH hkerO hρD hρK' le_sup_left h.inH₁.1 h3₁ hK₁
    (hnot h.inH₁.1 h3₁)
  have hP₂ := s1347_A6_parabolic hT2 hTH hKH hkerO hρD hρK' le_sup_right h.inH₂.1 h3₂ hK₂
    (hnot h.inH₂.1 h3₂)
  have hne : (H₁.subgroupOf (H₁ ⊔ H₂)).map ρ ≠ (H₂.subgroupOf (H₁ ⊔ H₂)).map ρ := by
    intro he
    apply h.ne
    have hk : ∀ {Hi : Subgroup G}, T ≤ Hi → ρ.ker ≤ Hi.subgroupOf (H₁ ⊔ H₂) := fun hTi g hg =>
      mem_subgroupOf.2 (hTi (hO₂T ((hkerO g).1 hg)))
    have hsub : H₁.subgroupOf (H₁ ⊔ H₂) = H₂.subgroupOf (H₁ ⊔ H₂) := by
      calc H₁.subgroupOf (H₁ ⊔ H₂) = comap ρ ((H₁.subgroupOf (H₁ ⊔ H₂)).map ρ) :=
            (comap_map_eq_self (hk h.inH₁.1)).symm
        _ = comap ρ ((H₂.subgroupOf (H₁ ⊔ H₂)).map ρ) := by rw [he]
        _ = H₂.subgroupOf (H₁ ⊔ H₂) := comap_map_eq_self (hk h.inH₂.1)
    have h1 := subgroupOf_inj.1 hsub
    rwa [inf_eq_left.2 le_sup_left, inf_eq_left.2 le_sup_right] at h1
  obtain ⟨u, hu, hu1⟩ := exists_ne_one_of_card_two hc₁
  obtain ⟨v, hv, hv1⟩ := exists_ne_one_of_card_two hc₂
  have hZ := s1347_Z_eq hZsup hc₁ hc₂ hu hu1 hv hv1
  have huZ : u ∈ quasithinOmegaOneCenter T := (mem_inf.1 hu).1
  have hvZ : v ∈ quasithinOmegaOneCenter T := (mem_inf.1 hv).1
  have hu₂ : u ∉ centralizer (H₂ : Set G) := fun h' => hu1 (by
    have : u ∈ cZ T H₁ ⊓ cZ T H₂ := mem_inf.2 ⟨hu, mem_inf.2 ⟨huZ, h'⟩⟩
    rwa [hZinf, mem_bot] at this)
  have hv₁ : v ∉ centralizer (H₁ : Set G) := fun h' => hv1 (by
    have : v ∈ cZ T H₁ ⊓ cZ T H₂ := mem_inf.2 ⟨mem_inf.2 ⟨hvZ, h'⟩, hv⟩
    rwa [hZinf, mem_bot] at this)
  obtain ⟨F₀, hF₀s, hF₀I, hF₀T, hF₀K⟩ : ∃ F₀ : ↥(v0Of T H₁ H₂) →* ↥W4, Function.Surjective F₀ ∧
      (∀ v : ↥(v0Of T H₁ H₂), (v : G) ∈ I → F₀ v = 1) ∧
      (∀ t (ht : t ∈ T) (v : ↥(v0Of T H₁ H₂)) (hv : t * v * t⁻¹ ∈ v0Of T H₁ H₂),
        F₀ ⟨t * v * t⁻¹, hv⟩ = act4 (S6Out.phiEquiv.symm (ρ ⟨t, hTH ht⟩)) (F₀ v)) ∧
      (∀ k (hk : k ∈ K₀) (v : ↥(v0Of T H₁ H₂)) (hv : k * v * k⁻¹ ∈ v0Of T H₁ H₂),
        F₀ ⟨k * v * k⁻¹, hv⟩ = act4 (S6Out.phiEquiv.symm (ρ ⟨k, hKH hk⟩)) (F₀ v)) := by
    rcases hP₁ with h1 | h1
    · have h2 := hP₂.resolve_left fun h2 => hne (h1.trans h2.symm)
      exact s1347_A6_top S hH₀ hKH hN hsup hIV hH₀I hIirr hψ hTH hρT hρK hkerV le_sup_left
        h1 h2 hu hv hv₁ hZ
    · have h2 := hP₂.resolve_right fun h2 => hne (h1.trans h2.symm)
      refine s1347_A6_top S hH₀ hKH hN hsup hIV hH₀I hIirr hψ hTH hρT hρK hkerV le_sup_right
        h2 h1 hv hu hu₂ (fun z hz => ?_)
      rcases hZ z hz with h' | h' | h' | h'
      · exact Or.inl h'
      · exact Or.inr (Or.inr (Or.inl h'))
      · exact Or.inr (Or.inl h')
      · exact Or.inr (Or.inr (Or.inr (h'.trans (s1347_Z_comm huZ hvZ))))
  refine ⟨I, hIc, hH₀I, ρ, ψ, F₀, hIV, hψ, fun g hg => hρT g hg, fun g hg => hρK' g hg, hkerV,
    hF₀s, hF₀I, fun g w hw hg => ?_⟩
  rcases hg with hgT | hgK
  · exact hF₀T g hgT w hw
  · exact hF₀K g hgK w hw

theorem s1347_concl_iv (hedge : GoldschmidtEdgeBoundS3) (h1332 : Stmt13_3_2)
    (h1228 : Stmt12_2_8) (hC58 : TheoremC58) (h317 : AS317Sylow) (h56 : AsB56)
    (h135 : A6.Stmt13_3_5) (h1345 : NQS134.Stmt13_4_5) (S : A6.Setting134 G T L V)
    {H₁ H₂ : Subgroup G} (h : Hyp1347 T H₁ H₂) (hns : ¬ Group.IsSolvable ↥(H₁ ⊔ H₂))
    {K₀ : Subgroup G} (hK₀ : K₀ ∈ cComp (H₁ ⊔ H₂)) (hN : H₁ ⊔ H₂ ≤ normalizer (K₀ : Set G))
    (hA6 : Nonempty (↥K₀ ⧸ CFSG.pCore 2 ↥K₀ ≃* alternatingGroup (Fin 6)))
    (hK₁ : oTwoRes H₁ ≤ K₀) (hK₂ : oTwoRes H₂ ≤ K₀) (hsup : H₁ ⊔ H₂ = K₀ ⊔ T)
    (hcentK : K₀ ⊓ centralizer (v0Of T H₁ H₂ : Set G) = pCoreOf 2 K₀) :
    Concl1347iv T H₁ H₂ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hH₀, -⟩ := s1347_one_first hedge h1332 h1228 hC58 h317 h56 h135 S h
  obtain ⟨I, hIc, hH₀I, ρ, ψ, F₀, hIV, hψ, hρT, -, hkerV, hF₀s, hF₀I, hF₀⟩ :=
    s1347_A6_data hedge h1332 h1228 hC58 h317 h56 h135 h1345 S h hns hK₀ hN hA6 hK₁ hK₂ hsup
      hcentK
  have hsyl₀ : IsSylowTwoOf T (H₁ ⊔ H₂) := A5.isSylowTwoOf_of_le S.h13.sylow hH₀.1
  have hTH : T ≤ H₁ ⊔ H₂ := hsyl₀.1
  have hO₂T : pCoreOf 2 (H₁ ⊔ H₂) ≤ T := pCoreOf_two_le_of_isSylowTwoOf hsyl₀
  have hred := s1347_reduced S hH₀
  have hI16 : Nat.card I = 16 := by
    rw [Nat.card_congr ψ.toEquiv]
    have h1 : Fintype.card {x : P6 // InW4 x} = 16 := by decide +kernel
    rw [← h1, ← Nat.card_eq_fintype_card]
    rfl
  have hoff : ∀ {j : ℕ}, j ≤ 1 → ∀ A, IsElemAbelianCorank T j A →
      A ≤ centralizer (v0Of T H₁ H₂ : Set G) := fun hj A hA =>
    le_centralizer_of_A6 hTH hred.2.2.1 (s1347_V0_le_T S hH₀) hIV hH₀I hI16 hψ
      (fun t ht => hρT ⟨t, hTH ht⟩ ht) hkerV hF₀s hF₀I
      (fun t ht x hx => hF₀ ⟨t, hTH ht⟩ x hx (Or.inl ht)) hj hA
  have hJ : ∀ {j : ℕ}, j ≤ 1 → H₁ ⊔ H₂ ≤ normalizer (thompsonJi T j : Set G) := fun hj =>
    le_normalizer_thompsonJi_of hO₂T (le_normalizer_pCoreOf 2 (H₁ ⊔ H₂)) fun A hA => by
      rw [← s1347_T_inf_centralizer S h hH₀]
      exact le_inf hA.1 (hoff hj A hA)
  exact ⟨K₀, hsup, hK₀, (quasithinO2QuotientIso_iff K₀ _).2 hA6, hJ (Nat.zero_le 1), hJ le_rfl⟩

end CFSG.Quasithin.H13.U3
