module

public import CFSG.Quasithin.H13.NQS13410E
public import CFSG.Quasithin.H13.NQS134Hat8

public section

namespace CFSG.Quasithin.H13.NQS134

open Subgroup Equiv CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.H13.A6

theorem k4_card_mul_lt_W4 : ∀ f : Fin 8 → Bool, (∀ i : Fin 8, 4 ≤ (i : ℕ) → f i = false) →
    (∃ i, i ≠ 0 ∧ f i = true) →
    (Finset.univ.filter (fun i => f i = true)).card *
      (Finset.univ.filter (fun x : P6 => InW4 x ∧
        ∀ i, f i = true → act4f (U3.k4xF i) x = x)).card < 16 := by
  decide +kernel

theorem act4f_faithful : ∀ σ : Perm (Fin 6), (∀ x : P6, InW4 x → act4f σ x = x) → σ = 1 := by
  decide +kernel

theorem permAct_core_faithful : ∀ σ : Perm (Fin 6),
    (∀ x : P6, ∑ i, Multiplicative.toAdd x i = 0 → G6.permAct 6 σ x = x) → σ = 1 := by
  decide +kernel

theorem sign_of_cube : ∀ σ : Perm (Fin 6), σ ^ 3 = 1 → Perm.sign σ = 1 := by decide +kernel

theorem stab45_conj_D_K4 : ∀ γ ∈ stab45List, γ ^ 3 = 1 → γ ≠ 1 → ∀ τ : Perm (Fin 6), InD6 τ →
    Perm.sign τ = 1 → InD6 (γ * τ * γ⁻¹) → τ ∈ U3.K4List := by
  decide +kernel

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

omit [Finite G] in
theorem exists_hatEquivK {K W : Subgroup G} (hKW : K ≤ normalizer (W : Set G))
    (ρ : ↥(normalizer (W : Set G)) →* Perm (Fin 6))
    (himg : ∀ σ : Perm (Fin 6), (∃ g : ↥(normalizer (W : Set G)), (g : G) ∈ K ∧ ρ g = σ) ↔
      σ ∈ alternatingGroup (Fin 6))
    (hker : ∀ g, ρ g = 1 ↔ (g : G) ∈ centralizer (W : Set G))
    (ho2Z : A6.o2Z K = K ⊓ centralizer (W : Set G)) :
    ∃ e : (↥K ⧸ CFSG.pCore 2 ↥K) ⧸ center (↥K ⧸ CFSG.pCore 2 ↥K) ≃*
        ↥(alternatingGroup (Fin 6)),
      ∀ k : ↥K, (e (((k : ↥K ⧸ CFSG.pCore 2 ↥K)) :
        (↥K ⧸ CFSG.pCore 2 ↥K) ⧸ center (↥K ⧸ CFSG.pCore 2 ↥K)) : Perm (Fin 6)) =
          ρ ⟨k, hKW k.2⟩ := by
  set f : ↥K →* ↥(alternatingGroup (Fin 6)) :=
    (ρ.comp (Subgroup.inclusion hKW)).codRestrict _
      (fun k => (himg _).1 ⟨Subgroup.inclusion hKW k, k.2, rfl⟩) with hf
  have hfv : ∀ k : ↥K, (f k : Perm (Fin 6)) = ρ ⟨k, hKW k.2⟩ := fun k => rfl
  have hmemZ : ∀ k : ↥K, (k : G) ∈ A6.o2Z K ↔
      ((k : ↥K ⧸ CFSG.pCore 2 ↥K)) ∈ center (↥K ⧸ CFSG.pCore 2 ↥K) := by
    intro k
    constructor
    · rintro ⟨k', hk', hkk'⟩
      have e : k' = k := Subtype.ext hkk'
      rw [← e]
      exact hk'
    · intro h
      exact ⟨k, h, rfl⟩
  have hO : ∀ x ∈ CFSG.pCore 2 ↥K, f x = 1 := by
    intro x hx
    apply Subtype.ext
    rw [hfv, Subgroup.coe_one]
    refine (hker _).2 ?_
    have h1 : (x : G) ∈ A6.o2Z K := by
      rw [hmemZ]
      rw [(QuotientGroup.eq_one_iff x).2 hx]
      exact one_mem _
    rw [ho2Z] at h1
    exact (mem_inf.1 h1).2
  set fq := QuotientGroup.lift (CFSG.pCore 2 ↥K) f hO with hfq
  have hfq_mk : ∀ k : ↥K, fq (k : ↥K ⧸ CFSG.pCore 2 ↥K) = f k := fun k => rfl
  have hsurj : Function.Surjective fq := by
    rintro ⟨σ, hσ⟩
    obtain ⟨g, hgK, hg⟩ := (himg σ).2 hσ
    refine ⟨((⟨g, hgK⟩ : ↥K) : ↥K ⧸ CFSG.pCore 2 ↥K), Subtype.ext ?_⟩
    rw [hfq_mk, hfv]
    exact hg
  have hkerq : fq.ker = center (↥K ⧸ CFSG.pCore 2 ↥K) := by
    ext q
    induction q using QuotientGroup.induction_on with
    | _ k =>
      rw [MonoidHom.mem_ker, hfq_mk, ← hmemZ, ho2Z]
      constructor
      · intro h
        refine mem_inf.2 ⟨k.2, (hker ⟨k, hKW k.2⟩).1 ?_⟩
        rw [← hfv, h, Subgroup.coe_one]
      · intro h
        apply Subtype.ext
        rw [hfv, Subgroup.coe_one]
        exact (hker _).2 (mem_inf.1 h).2
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hkerq.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective fq hsurj), fun k => rfl⟩

theorem rho_sign_of_comm (hInv : HatA6OddInverts) {K W : Subgroup G} (hhatK : A6.IsHatA6 K)
    (hKW : K ≤ normalizer (W : Set G)) (ρ : ↥(normalizer (W : Set G)) →* Perm (Fin 6))
    (himg : ∀ σ : Perm (Fin 6), (∃ g : ↥(normalizer (W : Set G)), (g : G) ∈ K ∧ ρ g = σ) ↔
      σ ∈ alternatingGroup (Fin 6))
    (hker : ∀ g, ρ g = 1 ↔ (g : G) ∈ centralizer (W : Set G))
    (ho2Z : A6.o2Z K = K ⊓ centralizer (W : Set G)) (r : ↥(normalizer (W : Set G)))
    (hrK : (r : G) ∈ normalizer (K : Set G))
    (hcomm : ∀ c ∈ A6.l0 K, c ^ 3 = 1 → c ∉ pCoreOf 2 K →
      ∃ k : ℕ, ((r : G) * c * (r : G)⁻¹ * c⁻¹) ^ 2 ^ k = 1) : Perm.sign (ρ r) = 1 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e, he⟩ := exists_hatEquivK hKW ρ himg hker ho2Z
  by_contra hs
  have hs' : Perm.sign (ρ r) = -1 := (Int.units_eq_one_or _).resolve_left hs
  set X := ↥K ⧸ CFSG.pCore 2 ↥K with hX
  set α := conjQuot (L := K) (⟨r, hrK⟩ : ↥(normalizer (K : Set G))) with hα
  have hcompat : ∀ x : X, ((e (α x : X ⧸ center X) : Perm (Fin 6))) =
      ρ r * (e (x : X ⧸ center X) : Perm (Fin 6)) * (ρ r)⁻¹ := by
    intro x
    induction x using QuotientGroup.induction_on with
    | _ l =>
      rw [hα, conjQuot_mk, he, he]
      have e1 : (⟨((conjAct K ⟨r, hrK⟩ l : ↥K) : G), hKW (conjAct K ⟨r, hrK⟩ l).2⟩ :
          ↥(normalizer (W : Set G))) = r * ⟨l, hKW l.2⟩ * r⁻¹ :=
        Subtype.ext (A5.conjAct_val K ⟨r, hrK⟩ l)
      rw [e1, map_mul, map_mul, map_inv]
  have hinv := hInv X hhatK.1 hhatK.2.1 e α (ρ r) hs' hcompat
  obtain ⟨c, hcL0, hc3, hcO, -⟩ := A6.exists_l0_c hhatK.2.1
  have hcZ : c ∈ A6.o2Z K := oTwoRes_le _ hcL0
  obtain ⟨k, hk⟩ := hcomm c hcL0 hc3 hcO
  obtain ⟨c', hc'Z, hc'c⟩ := hcZ
  have hc'c' : (c' : G) = c := hc'c
  rw [← hc'c'] at hc3 hcO hk
  have hc'Z' : (c' : X) ∈ center X := hc'Z
  have h1 : α (c' : X) = (c' : X)⁻¹ := hinv _ hc'Z'
  set d : ↥K := conjAct K ⟨r, hrK⟩ c' * c'⁻¹ with hd
  have hdG : (d : G) = (r : G) * c' * (r : G)⁻¹ * (c' : G)⁻¹ := by
    rw [hd, Subgroup.coe_mul, A5.conjAct_val, Subgroup.coe_inv]
  have hd2 : d ^ 2 ^ k = 1 := Subtype.ext (by rw [Subgroup.coe_pow, hdG, hk, Subgroup.coe_one])
  have hdX : (d : X) = (c' : X)⁻¹ * (c' : X)⁻¹ := by
    rw [hd, QuotientGroup.mk_mul, QuotientGroup.mk_inv, ← conjQuot_mk, ← hα, h1]
  have hc3' : (c' : X) ^ 3 = 1 := by
    rw [← QuotientGroup.mk_pow]
    have : c' ^ 3 = 1 := Subtype.ext (by rw [Subgroup.coe_pow, hc3, Subgroup.coe_one])
    rw [this, QuotientGroup.mk_one]
  have hcX : (c' : X)⁻¹ * (c' : X)⁻¹ = (c' : X) := by
    calc (c' : X)⁻¹ * (c' : X)⁻¹ = (c' : X)⁻¹ * (c' : X)⁻¹ * (c' : X) ^ 3 := by
          rw [hc3', mul_one]
      _ = (c' : X) := by group
  have hc2 : (c' : X) ^ 2 ^ k = 1 := by
    rw [← hcX, ← hdX, ← QuotientGroup.mk_pow, hd2, QuotientGroup.mk_one]
  have hc1 : (c' : X) = 1 := by
    have h2 : orderOf (c' : X) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hc2
    have h3 : orderOf (c' : X) ∣ 3 := orderOf_dvd_of_pow_eq_one hc3'
    have h4 : Nat.Coprime (2 ^ k) 3 := Nat.Coprime.pow_left k (by norm_num)
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes h4 h2 h3)
  exact hcO ((A6.mem_pCore_iff c').1 ((QuotientGroup.eq_one_iff _).1 hc1))

theorem relIndex_mul_card_le_count {A W : Subgroup G}
    (ρ : ↥(normalizer (W : Set G)) →* Perm (Fin 6))
    (hker : ∀ g, ρ g = 1 ↔ (g : G) ∈ centralizer (W : Set G))
    (actf : Perm (Fin 6) → P6 → P6) (InM : P6 → Prop) [DecidablePred InM] (ψf : ↥W → P6)
    (hψ : Function.Injective ψf) (hInM : ∀ w, InM (ψf w))
    (hfix : ∀ (g : ↥(normalizer (W : Set G))) (w : ↥W),
      (g : G) * w * (g : G)⁻¹ = w ↔ actf (ρ g) (ψf w) = ψf w)
    (hAN : A ≤ normalizer (W : Set G))
    (hAK : ∀ a : ↥(normalizer (W : Set G)), (a : G) ∈ A → ρ a ∈ U3.K4xList) :
    ∃ f : Fin 8 → Bool,
      (∀ i, f i = true ↔ ∃ a : ↥(normalizer (W : Set G)), (a : G) ∈ A ∧ ρ a = U3.k4xF i) ∧
      (A ⊓ centralizer (W : Set G)).relIndex A * Nat.card ↥(W ⊓ centralizer (A : Set G)) ≤
        (Finset.univ.filter (fun i => f i = true)).card *
          (Finset.univ.filter (fun x : P6 => InM x ∧
            ∀ i, f i = true → actf (U3.k4xF i) x = x)).card := by
  classical
  have hinj := U3.k4xF_inj
  have hsurj := U3.k4xF_surj
  let f : Fin 8 → Bool := fun i =>
    decide (∃ a : ↥(normalizer (W : Set G)), (a : G) ∈ A ∧ ρ a = U3.k4xF i)
  have hf : ∀ i, f i = true ↔
      ∃ a : ↥(normalizer (W : Set G)), (a : G) ∈ A ∧ ρ a = U3.k4xF i := fun i =>
    decide_eq_true_iff
  refine ⟨f, hf, Nat.mul_le_mul ?_ ?_⟩
  ·
    rw [← card_autOn_eq_relIndex hAN]
    set X := (A.subgroupOf (normalizer (W : Set G))).map ρ with hX
    have hconj : ∀ n, conjAct W n = 1 ↔ ρ n = 1 := fun n => by
      rw [A4.conjAct_eq_one_iff, hker]
    have h1 : Nat.card ↥(autOn A W) = Nat.card ↥X :=
      Nat.card_congr (U3.mapMulEquivOfKer (conjAct W) ρ hconj
        (A.subgroupOf (normalizer (W : Set G)))).toEquiv
    rw [h1]
    let g : {i : Fin 8 // f i = true} → ↥X := fun i => ⟨U3.k4xF i.1, by
      obtain ⟨a, ha, hρ⟩ := (hf i.1).1 i.2
      exact ⟨a, mem_subgroupOf.2 ha, hρ⟩⟩
    have hg : Function.Surjective g := by
      rintro ⟨σ, a, ha, hρ⟩
      obtain ⟨i, hi⟩ := hsurj _ (hAK a (mem_subgroupOf.1 ha))
      exact ⟨⟨i, (hf i).2 ⟨a, mem_subgroupOf.1 ha, hi.symm⟩⟩, Subtype.ext (hi.trans hρ)⟩
    have h3 := Nat.card_le_card_of_surjective g hg
    rwa [Nat.card_eq_fintype_card (α := {i : Fin 8 // f i = true}), Fintype.card_subtype] at h3
  ·
    refine card_le_of_maps_to (fun w : ↥(W ⊓ centralizer (A : Set G)) => ψf ⟨w, w.2.1⟩)
      (fun a b hab => Subtype.ext (by
        have h := hψ hab
        exact congrArg (fun x : ↥W => (x : G)) h)) _ fun w => ?_
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, hInM _, fun i hi => ?_⟩
    obtain ⟨a, ha, hρ⟩ := (hf i).1 hi
    have hc : (a : G) * w * (a : G)⁻¹ = w := by
      rw [mem_centralizer_iff.mp w.2.2 a ha, mul_inv_cancel_right]
    rw [← hρ]
    exact (hfix a ⟨w, w.2.1⟩).1 hc

theorem relIndex_mul_card_lt_of_count {A W : Subgroup G}
    (ρ : ↥(normalizer (W : Set G)) →* Perm (Fin 6))
    (hker : ∀ g, ρ g = 1 ↔ (g : G) ∈ centralizer (W : Set G))
    (actf : Perm (Fin 6) → P6 → P6) (InM : P6 → Prop) [DecidablePred InM] (ψf : ↥W → P6)
    (hψ : Function.Injective ψf) (hInM : ∀ w, InM (ψf w))
    (hfix : ∀ (g : ↥(normalizer (W : Set G))) (w : ↥W),
      (g : G) * w * (g : G)⁻¹ = w ↔ actf (ρ g) (ψf w) = ψf w) {n : ℕ}
    (hdec : ∀ f : Fin 8 → Bool, (∀ i : Fin 8, 4 ≤ (i : ℕ) → f i = false) →
      (∃ i, i ≠ 0 ∧ f i = true) →
      (Finset.univ.filter (fun i => f i = true)).card *
        (Finset.univ.filter (fun x : P6 => InM x ∧
          ∀ i, f i = true → actf (U3.k4xF i) x = x)).card < n)
    (hAN : A ≤ normalizer (W : Set G))
    (hAK : ∀ a : ↥(normalizer (W : Set G)), (a : G) ∈ A → ρ a ∈ U3.K4List)
    (hA : ¬ A ≤ centralizer (W : Set G)) :
    (A ⊓ centralizer (W : Set G)).relIndex A * Nat.card ↥(W ⊓ centralizer (A : Set G)) < n := by
  have hsurj := U3.k4xF_surj
  have h0 := U3.k4xF_zero
  have h4 := U3.k4xF_not_K4
  have hK4x := U3.K4_le_K4x
  obtain ⟨f, hf, hle⟩ := relIndex_mul_card_le_count ρ hker actf InM ψf hψ hInM hfix hAN
    fun a ha => hK4x _ (hAK a ha)
  refine hle.trans_lt (hdec f (fun i hi => ?_) ?_)
  · by_contra hfi
    obtain ⟨a, ha, hρ⟩ := (hf i).1 (Bool.not_eq_false _ ▸ hfi)
    exact h4 i hi (hρ ▸ hAK a ha)
  · obtain ⟨x, hxA, hxC⟩ := IsConcreteLE.not_le_iff_exists.1 hA
    obtain ⟨i, hi⟩ := hsurj _ (hK4x _ (hAK ⟨x, hAN hxA⟩ hxA))
    refine ⟨i, fun h0i => hxC ?_, (hf i).2 ⟨⟨x, hAN hxA⟩, hxA, hi.symm⟩⟩
    rw [h0i, h0] at hi
    exact (hker ⟨x, hAN hxA⟩).1 hi.symm

theorem mem_K_of_orderOf_three_of_hat (h1332 : Stmt13_3_2) (h1228 : Stmt12_2_8)
    (S : A6.Setting134 G T L V) {K W : Subgroup G} (hKf : quasithinIsFaithfulLocal T K)
    (hhatK : A6.IsHatA6 K) (hW : IsIrrPlusIn K (reducedAggregate (K ⊔ T)) T W) {x : G}
    (hx : x ∈ normalizer (K : Set G)) (hx3 : orderOf x = 3) : x ∈ K := by
  obtain ⟨-, hz, ⟨e⟩⟩ := hhatK
  have h360 : Nat.card ↥(alternatingGroup (Fin 6)) = 360 := by
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
    decide
  have h60 : Nat.card ↥(alternatingGroup (Fin 5)) = 60 := by
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
    decide
  have hc : Nat.card (↥K ⧸ CFSG.pCore 2 ↥K) = 1080 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup
      (center (↥K ⧸ CFSG.pCore 2 ↥K))
    rw [Nat.card_congr e.toEquiv, h360, hz] at h1
    rw [h1]
  have hH : QTH13 G T K :=
    { simple := S.h13.simple
      nonabelian := S.h13.nonabelian
      qtke := S.h13.qtke
      sylow := S.h13.sylow
      faithful := hKf
      not_excluded := S.h13.not_excluded
      a5 := fun ⟨φ, hφs, hφk⟩ => by
        exfalso
        have h1 := Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective φ hφs).toEquiv
        rw [hφk, hc, h60] at h1
        omega }
  have hyp := U3.hyp1223_of h1332 hH hW
  rcases h1228 G T K W hyp with h | h | ⟨-, h⟩
  · rw [← h]
    exact subset_closure ⟨hx, 1, by rw [pow_one, ← hx3, pow_orderOf_eq_one]⟩
  · exfalso
    rcases h with he5 | h32
    · obtain ⟨e5⟩ := he5
      have := Nat.card_congr e5.toEquiv
      rw [h60] at this
      omega
    · obtain ⟨e3⟩ := nonempty_equiv_SL32_of_lieModel h32
      have := Nat.card_congr e3.toEquiv
      rw [HSType.card_SL_three_two] at this
      omega
  · rw [h]
    exact subset_closure ⟨hx, hx3⟩

end CFSG.Quasithin.H13.NQS134
