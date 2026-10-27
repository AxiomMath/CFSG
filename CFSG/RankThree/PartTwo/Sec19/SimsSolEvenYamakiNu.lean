module

public import CFSG.RankThree.PartTwo.Sec19.SimsSolEvenYamakiFusion
import CFSG.RankThree.PartTwo.Sec19.SimsSolEvenYamakiNuFano
import CFSG.RankThree.PartTwo.Sec19.SimsSolEvenYamakiNuVec
import CFSG.ClassicalInvolution.Sp62Rec.ModelCR1NA
import CFSG.ClassicalInvolution.Sp62Rec.ModelCR1E64
public import CFSG.LargeExtraspecial.DWModelSplit

public section

namespace CFSG.RankThree.PartTwo.Sec19.SolEven.YamakiRec

open CFSG.ClassicalInvolution.Solomon73 CFSG.ClassicalInvolution.Solomon73.Yamaki
open CFSG.ClassicalInvolution.Sp62Rec CFSG.ClassicalInvolution.Q3.AE CFSG.Open
open CFSG.RankThree.PartTwo.Sec19.SolEven.Yamaki (FusionOut)

variable
  {G : Type} [Group G] [Finite G] {z : G}

section Basic

variable (F : FusionOut z)

theorem θ_mem_A0 {x : G} (hx : x ∈ F.A) :
    (F.θ ⟨x, F.A_le hx⟩ : StatedSp 3 (ZMod 2)) ∈ A0 :=
  (F.θ_A x (F.A_le hx)).mp hx

theorem A_comm : ∀ x ∈ F.A, ∀ y ∈ F.A, x * y = y * x := by
  intro x hx y hy
  have h := isE64_A0.1 _ (θ_mem_A0 F hx) _ (θ_mem_A0 F hy)
  have h2 : F.θ (⟨x, F.A_le hx⟩ * ⟨y, F.A_le hy⟩) = F.θ (⟨y, F.A_le hy⟩ * ⟨x, F.A_le hx⟩) := by
    apply Subtype.ext
    simp only [map_mul, Subgroup.coe_mul]
    exact h
  exact congrArg Subtype.val (F.θ.injective h2)

theorem A_sq : ∀ x ∈ F.A, x * x = 1 := by
  intro x hx
  have h := isE64_A0.2.1 _ (θ_mem_A0 F hx)
  have h2 : F.θ (⟨x, F.A_le hx⟩ * ⟨x, F.A_le hx⟩) = F.θ 1 := by
    apply Subtype.ext
    simp only [map_mul, Subgroup.coe_mul, map_one, OneMemClass.coe_one]
    exact h
  exact congrArg Subtype.val (F.θ.injective h2)

noncomputable def equivA0 : ↥F.A ≃ ↥A0 where
  toFun x := ⟨F.θ ⟨x, F.A_le x.2⟩, θ_mem_A0 F x.2⟩
  invFun a := ⟨F.θ.symm ⟨a, A0_le_Hhat a.2⟩, (F.θ_A _ (F.θ.symm ⟨a, A0_le_Hhat a.2⟩).2).mpr (by
    rw [Subtype.coe_eta, MulEquiv.apply_symm_apply]
    exact a.2)⟩
  left_inv x := by
    apply Subtype.ext
    simp only [Subtype.coe_eta, MulEquiv.symm_apply_apply]
  right_inv a := by
    apply Subtype.ext
    simp only [Subtype.coe_eta, MulEquiv.apply_symm_apply]

theorem card_A : Nat.card F.A = 64 := by
  rw [Nat.card_congr (equivA0 F), card_A0]

noncomputable def equivS0 : ↥(F.T : Subgroup G) ≃ ↥S0 where
  toFun x := ⟨F.θ ⟨x, F.T_le x.2⟩, (F.θ_T x (F.T_le x.2)).mp x.2⟩
  invFun a := ⟨F.θ.symm ⟨a, S0_le_Hhat a.2⟩, (F.θ_T _ (F.θ.symm ⟨a, S0_le_Hhat a.2⟩).2).mpr (by
    rw [Subtype.coe_eta, MulEquiv.apply_symm_apply]
    exact a.2)⟩
  left_inv x := by
    apply Subtype.ext
    simp only [Subtype.coe_eta, MulEquiv.symm_apply_apply]
  right_inv a := by
    apply Subtype.ext
    simp only [Subtype.coe_eta, MulEquiv.apply_symm_apply]

theorem card_T : Nat.card (F.T : Subgroup G) = 512 := by
  rw [Nat.card_congr (equivS0 F), card_S0]

theorem T_le_normalizer : (F.T : Subgroup G) ≤ Subgroup.normalizer (F.A : Set G) := by
  intro t ht
  have htC := F.T_le ht
  have hθt : (F.θ ⟨t, htC⟩ : StatedSp 3 (ZMod 2)) ∈ N0 := S0_le_N0 ((F.θ_T t htC).mp ht)
  have key : ∀ c (hc : c ∈ Subgroup.centralizer ({z} : Set G)),
      (F.θ ⟨c, hc⟩ : StatedSp 3 (ZMod 2)) ∈ N0 → ∀ a ∈ F.A, c * a * c⁻¹ ∈ F.A := by
    intro c hc hθc a ha
    have haC := F.A_le ha
    have hcaC : c * a * c⁻¹ ∈ Subgroup.centralizer ({z} : Set G) :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hc haC) (Subgroup.inv_mem _ hc)
    refine (F.θ_A _ hcaC).mpr ?_
    have e : (⟨c * a * c⁻¹, hcaC⟩ : ↥(Subgroup.centralizer ({z} : Set G))) =
        ⟨c, hc⟩ * ⟨a, haC⟩ * ⟨c, hc⟩⁻¹ := rfl
    rw [e, map_mul, map_mul, map_inv]
    exact (Subgroup.mem_normalizer_iff.mp (N0_le_normalizer hθc) _).mp (θ_mem_A0 F ha)
  rw [Subgroup.mem_normalizer_iff]
  intro a
  refine ⟨key t htC hθt a, fun ha => ?_⟩
  have htC' : t⁻¹ ∈ Subgroup.centralizer ({z} : Set G) := Subgroup.inv_mem _ htC
  have hθt' : (F.θ ⟨t⁻¹, htC'⟩ : StatedSp 3 (ZMod 2)) ∈ N0 := by
    have : (⟨t⁻¹, htC'⟩ : ↥(Subgroup.centralizer ({z} : Set G))) = (⟨t, htC⟩)⁻¹ := rfl
    rw [this, map_inv]
    exact Subgroup.inv_mem _ hθt
  have := key t⁻¹ htC' hθt' _ ha
  simpa [mul_assoc] using this

theorem b_mem_A (i : Fin 7) : F.b i ∈ F.A := by
  rw [← F.b_closure]
  exact Subgroup.subset_closure ⟨i, rfl⟩

theorem z_mem_A : z ∈ F.A := by
  obtain ⟨i, hi⟩ := F.z_mem
  have h := b_mem_A F i
  rwa [hi] at h

theorem z_mem_normalizer : z ∈ Subgroup.normalizer (F.A : Set G) :=
  Subgroup.le_normalizer (z_mem_A F)

end Basic

section Perm

variable (F : FusionOut z)

private theorem perm_unique {n : G} {σ τ : Equiv.Perm (Fin 7)}
    (hσ : ∀ i, n * F.b i * n⁻¹ = F.b (σ i)) (hτ : ∀ i, n * F.b i * n⁻¹ = F.b (τ i)) : σ = τ :=
  Equiv.ext fun i => F.b_inj ((hσ i).symm.trans (hτ i))

private theorem perm_spec (n : ↥(Subgroup.normalizer (F.A : Set G))) :
    Classical.choose (F.perm_mem n n.2) ∈ l32 ∧
      ∀ i, (n : G) * F.b i * (n : G)⁻¹ = F.b (Classical.choose (F.perm_mem n n.2) i) :=
  Classical.choose_spec (F.perm_mem n n.2)

noncomputable def permN : ↥(Subgroup.normalizer (F.A : Set G)) →* Equiv.Perm (Fin 7) where
  toFun n := Classical.choose (F.perm_mem n n.2)
  map_one' := perm_unique F (perm_spec F 1).2 fun i => by simp
  map_mul' n m := perm_unique F (perm_spec F (n * m)).2 fun i => by
    rw [Equiv.Perm.mul_apply, ← (perm_spec F n).2, ← (perm_spec F m).2]
    simp only [Subgroup.coe_mul, mul_inv_rev]
    group

theorem permN_spec (n : ↥(Subgroup.normalizer (F.A : Set G))) (i : Fin 7) :
    (n : G) * F.b i * (n : G)⁻¹ = F.b (permN F n i) :=
  (perm_spec F n).2 i

theorem permN_mem (n : ↥(Subgroup.normalizer (F.A : Set G))) : permN F n ∈ l32 :=
  (perm_spec F n).1

theorem permN_eq_one_iff (n : ↥(Subgroup.normalizer (F.A : Set G))) :
    permN F n = 1 ↔ (n : G) ∈ F.A := by
  constructor
  · intro h
    apply F.cent_A
    have hA : Subgroup.closure (Set.range F.b) ≤ Subgroup.centralizer ({(n : G)} : Set G) := by
      refine (Subgroup.closure_le _).mpr ?_
      rintro _ ⟨i, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      have hi := permN_spec F n i
      rw [h, Equiv.Perm.one_apply] at hi
      calc F.b i * (n : G) = (n : G) * F.b i * (n : G)⁻¹ * n := by rw [hi]
        _ = (n : G) * F.b i := by group
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    have ha' : a ∈ Subgroup.closure (Set.range F.b) := by rw [F.b_closure]; exact ha
    exact Subgroup.mem_centralizer_singleton_iff.mp (hA ha')
  · intro hn
    refine perm_unique F (perm_spec F n).2 fun i => ?_
    rw [Equiv.Perm.one_apply, A_comm F _ hn _ (b_mem_A F i), mul_inv_cancel_right]

end Perm

section Compl

variable (F : FusionOut z)

theorem exists_compl : ∃ L : Subgroup ↥(Subgroup.normalizer (F.A : Set G)),
    F.A.subgroupOf (Subgroup.normalizer (F.A : Set G)) ⊓ L = ⊥ ∧
      F.A.subgroupOf (Subgroup.normalizer (F.A : Set G)) ⊔ L = ⊤ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hAN : F.A ≤ Subgroup.normalizer (F.A : Set G) := Subgroup.le_normalizer
  have hTN := T_le_normalizer F
  haveI : (F.A.subgroupOf (Subgroup.normalizer (F.A : Set G))).Normal :=
    Subgroup.normal_in_normalizer
  haveI : IsMulCommutative ↥(F.A.subgroupOf (Subgroup.normalizer (F.A : Set G))) :=
    ⟨⟨fun x y => Subtype.ext (Subtype.ext (A_comm F _ x.2 _ y.2))⟩⟩
  have hV2 : IsPGroup 2 ↥(F.A.subgroupOf (Subgroup.normalizer (F.A : Set G))) := by
    refine IsPGroup.of_card (n := 6) ?_
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAN).toEquiv, card_A F]
    norm_num
  have hT2 : IsPGroup 2 ↥((F.T : Subgroup G).subgroupOf (Subgroup.normalizer (F.A : Set G))) := by
    refine IsPGroup.of_card (n := 9) ?_
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTN).toEquiv, card_T F]
    norm_num
  have hidx : ¬ 2 ∣ ((F.T : Subgroup G).subgroupOf (Subgroup.normalizer (F.A : Set G))).index := by
    have h := Subgroup.index_mul_card
      ((F.T : Subgroup G).subgroupOf (Subgroup.normalizer (F.A : Set G)))
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTN).toEquiv, card_T F, F.card_N] at h
    have h21 : ((F.T : Subgroup G).subgroupOf (Subgroup.normalizer (F.A : Set G))).index = 21 := by
      omega
    rw [h21]
    decide
  let P : Sylow 2 ↥(Subgroup.normalizer (F.A : Set G)) := hT2.toSylow hidx
  obtain ⟨U, hUT, hUA, hUAT⟩ := F.compl
  have hUN : U ≤ Subgroup.normalizer (F.A : Set G) := hUT.trans hTN
  refine (CFSG.Quasithin.gaschutz hV2 P).mpr
    ⟨U.subgroupOf (Subgroup.normalizer (F.A : Set G)), ?_, ?_, ?_⟩
  · intro x hx
    exact hUT hx
  · rw [eq_bot_iff]
    rintro x ⟨hxA, hxU⟩
    have h1 : (x : G) ∈ U ⊓ F.A := ⟨hxU, hxA⟩
    rw [hUA] at h1
    exact (Subgroup.mem_bot).mpr (Subtype.ext h1)
  · show _ = (F.T : Subgroup G).subgroupOf (Subgroup.normalizer (F.A : Set G))
    rw [← Subgroup.subgroupOf_sup hAN hUN, sup_comm, hUAT]

end Compl

structure NuData (F : FusionOut z) where
  vec : ↥F.A →* Multiplicative (Fin 7 → ZMod 2)
  vec_inj : Function.Injective vec
  vec_even : ∀ x, ∑ i, Multiplicative.toAdd (vec x) i = 0
  vec_conj : ∀ (f : ↥F.A →* ↥F.A) (σ : Equiv.Perm (Fin 7)),
    (∀ i, f ⟨F.b i, b_mem_A F i⟩ = ⟨F.b (σ i), b_mem_A F (σ i)⟩) →
      ∀ x, Multiplicative.toAdd (vec (f x)) = fun j => Multiplicative.toAdd (vec x) (σ.symm j)
  s : ↥(Subgroup.normalizer (F.A : Set G)) →* ↥(Subgroup.normalizer (F.A : Set G))
  s_perm : ∀ n, permN F (s n) = permN F n
  s_one : ∀ n, permN F n = 1 → s n = 1

section NuData

variable (F : FusionOut z)

theorem nonempty_nuData : Nonempty (NuData F) := by
  obtain ⟨vec, hinj, heven, -, hconj⟩ := exists_vec (A_comm F) (A_sq F) (card_A F) F.b
    (b_mem_A F) F.b_prod F.b_closure
  obtain ⟨L, hAL, hALt⟩ := exists_compl F
  set σL := (permN F).comp L.subtype with hσL
  have hinjL : Function.Injective σL := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro ℓ hℓ
    have h1 : ((ℓ : ↥(Subgroup.normalizer (F.A : Set G))) : G) ∈ F.A :=
      (permN_eq_one_iff F _).mp hℓ
    have h2 : (ℓ : ↥(Subgroup.normalizer (F.A : Set G))) ∈
        F.A.subgroupOf (Subgroup.normalizer (F.A : Set G)) ⊓ L := ⟨h1, ℓ.2⟩
    rw [hAL, Subgroup.mem_bot] at h2
    exact (Subgroup.mem_bot).mpr (Subtype.ext h2)
  have hrange : (permN F).range = σL.range := by
    refine le_antisymm ?_ (fun _ ⟨ℓ, hℓ⟩ => ⟨ℓ, hℓ⟩)
    rintro _ ⟨n, rfl⟩
    have hn : n ∈ F.A.subgroupOf (Subgroup.normalizer (F.A : Set G)) ⊔ L := by
      rw [hALt]; exact Subgroup.mem_top n
    obtain ⟨a, ha, ℓ, hℓ, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hn
    refine ⟨⟨ℓ, hℓ⟩, ?_⟩
    show permN F ℓ = permN F (a * ℓ)
    rw [map_mul, (permN_eq_one_iff F a).mpr ha, one_mul]
  let e := MonoidHom.ofInjective hinjL
  let sec : ↥(Subgroup.normalizer (F.A : Set G)) →* ↥(Subgroup.normalizer (F.A : Set G)) :=
    L.subtype.comp (e.symm.toMonoidHom.comp
      ((MulEquiv.subgroupCongr hrange).toMonoidHom.comp (permN F).rangeRestrict))
  have hsec : ∀ n, σL (e.symm ⟨permN F n, hrange ▸ ⟨n, rfl⟩⟩) = permN F n := by
    intro n
    have := congrArg Subtype.val (e.apply_symm_apply ⟨permN F n, hrange ▸ ⟨n, rfl⟩⟩)
    exact this
  refine ⟨⟨vec, hinj, heven, hconj, sec, fun n => ?_, fun n hn => ?_⟩⟩
  · exact hsec n
  · show L.subtype (e.symm ((MulEquiv.subgroupCongr hrange) ((permN F).rangeRestrict n))) = 1
    have h1 : (permN F).rangeRestrict n = 1 := Subtype.ext hn
    rw [h1, map_one, map_one, map_one]

end NuData

section Psi

variable {F : FusionOut z} (D : NuData F)

theorem mul_s_inv_mem (n : ↥(Subgroup.normalizer (F.A : Set G))) :
    ((n * (D.s n)⁻¹ : ↥(Subgroup.normalizer (F.A : Set G))) : G) ∈ F.A :=
  (permN_eq_one_iff F _).mp (by rw [map_mul, map_inv, D.s_perm, mul_inv_cancel])

@[expose] noncomputable def aN (n : ↥(Subgroup.normalizer (F.A : Set G))) : ↥F.A :=
  ⟨_, mul_s_inv_mem D n⟩

theorem coe_aN (n : ↥(Subgroup.normalizer (F.A : Set G))) :
    ((aN D n : ↥F.A) : G) = (n : G) * ((D.s n : ↥(Subgroup.normalizer (F.A : Set G))) : G)⁻¹ :=
  rfl

omit D in
@[expose] def conjA (n : ↥(Subgroup.normalizer (F.A : Set G))) : ↥F.A →* ↥F.A where
  toFun x := ⟨(n : G) * x * (n : G)⁻¹, (Subgroup.mem_normalizer_iff.mp n.2 x).mp x.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by simp only [Subgroup.coe_mul]; group)

omit D in
theorem conjA_b (n : ↥(Subgroup.normalizer (F.A : Set G))) (i : Fin 7) :
    conjA n ⟨F.b i, b_mem_A F i⟩ = ⟨F.b (permN F n i), b_mem_A F _⟩ :=
  Subtype.ext (permN_spec F n i)

theorem aN_mul (n m : ↥(Subgroup.normalizer (F.A : Set G))) :
    aN D (n * m) = conjA n (aN D m) * aN D n := by
  apply Subtype.ext
  simp only [coe_aN, conjA, MonoidHom.coe_mk, OneHom.coe_mk, Subgroup.coe_mul, map_mul,
    mul_inv_rev, Subgroup.coe_inv]
  group

@[expose] noncomputable def psi : ↥(Subgroup.normalizer (F.A : Set G)) →* Wr 7 where
  toFun n := ⟨Multiplicative.toAdd (D.vec (aN D n)), permN F n⟩
  map_one' := by
    have h1 : aN D 1 = 1 := Subtype.ext (by simp [coe_aN, map_one])
    refine Wr.ext ?_ (map_one (permN F))
    rw [h1, map_one]
    rfl
  map_mul' n m := by
    refine Wr.ext (funext fun i => ?_) (map_mul (permN F) n m)
    show Multiplicative.toAdd (D.vec (aN D (n * m))) i =
      Multiplicative.toAdd (D.vec (aN D n)) i +
        Multiplicative.toAdd (D.vec (aN D m)) ((permN F n).symm i)
    rw [aN_mul, map_mul, toAdd_mul, Pi.add_apply,
      D.vec_conj (conjA n) (permN F n) (conjA_b n) (aN D m), add_comm]

theorem psi_injective : Function.Injective (psi D) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro n hn
  have hn' : psi D n = 1 := hn
  have hperm : permN F n = 1 := congrArg Wr.perm hn'
  have hvec : Multiplicative.toAdd (D.vec (aN D n)) = 0 := congrArg Wr.vec hn'
  have hs : D.s n = 1 := D.s_one n hperm
  have ha : aN D n = 1 := D.vec_inj (by rw [map_one]; exact hvec)
  have h1 := congrArg Subtype.val ha
  rw [coe_aN, hs, OneMemClass.coe_one, inv_one, mul_one] at h1
  exact (Subgroup.mem_bot).mpr (Subtype.ext h1)

end Psi

@[expose] def s7Sub : Subgroup (Wr 7) where
  carrier := {x | Wr.wsum x = 0 ∧ x.perm ∈ l32}
  mul_mem' {a b} ha hb := ⟨by rw [wsum_mul, ha.1, hb.1, add_zero], l32.mul_mem ha.2 hb.2⟩
  one_mem' := ⟨wsum_one, l32.one_mem⟩
  inv_mem' {a} ha := ⟨by rw [wsum_inv]; exact ha.1, l32.inv_mem ha.2⟩

theorem card_s7Sub_le : Nat.card s7Sub ≤ 10752 := by
  have hinj : Function.Injective fun a : ↥s7Sub =>
      ((⟨(a : Wr 7).vec, a.2.1⟩ : {v : Fin 7 → ZMod 2 // ∑ i, v i = 0}),
        (⟨(a : Wr 7).perm, a.2.2⟩ : ↥l32)) := by
    intro a b hab
    have h1 := congrArg (fun p => (p.1 : Fin 7 → ZMod 2)) hab
    have h2 := congrArg (fun p => (p.2 : Equiv.Perm (Fin 7))) hab
    exact Subtype.ext (Wr.ext h1 h2)
  have h := Nat.card_le_card_of_injective _ hinj
  rw [Nat.card_prod, card_evenVec] at h
  have h168 := card_l32_le
  omega

theorem aeSubOver_l32_le_s7Sub : aeSubOver l32 ≤ s7Sub := fun _ hx =>
  ⟨(mem_aeSub.mp hx.1).1, hx.2⟩

section Nu0

variable (F : FusionOut z)

theorem nonempty_nu0 : Nonempty (↥(Subgroup.normalizer (F.A : Set G)) ≃* ↥N0) := by
  obtain ⟨D⟩ := nonempty_nuData F
  obtain ⟨φ, hφ, hφmem⟩ := exists_hom_N0
  have hΨr : (psi D).range = s7Sub := by
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro _ ⟨n, rfl⟩
      refine ⟨D.vec_even (aN D n), permN_mem F n⟩
    · rw [Nat.card_congr (MonoidHom.ofInjective (psi_injective D)).toEquiv.symm, F.card_N]
      exact card_s7Sub_le
  have hφr : φ.range = s7Sub := by
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro _ ⟨x, rfl⟩
      exact aeSubOver_l32_le_s7Sub (hφmem x)
    · rw [Nat.card_congr (MonoidHom.ofInjective hφ).toEquiv.symm, card_N0]
      exact card_s7Sub_le
  exact ⟨(MonoidHom.ofInjective (psi_injective D)).trans
    ((MulEquiv.subgroupCongr (hΨr.trans hφr.symm)).trans (MonoidHom.ofInjective hφ).symm)⟩

end Nu0

section Orbit

theorem orbN0_eq_of_mem {x y : StatedSp 3 (ZMod 2)} (h : x ∈ orbN0 y) : orbN0 x = orbN0 y := by
  obtain ⟨m, hm, rfl⟩ := h
  ext w
  constructor
  · rintro ⟨n, hn, rfl⟩
    exact ⟨n * m, N0.mul_mem hn hm, by group⟩
  · rintro ⟨n, hn, rfl⟩
    exact ⟨n * m⁻¹, N0.mul_mem hn (N0.inv_mem hm), by group⟩

theorem mem_orbN0_alpha_of {x : StatedSp 3 (ZMod 2)} (hx : x ∈ A0) (hx1 : x ≠ 1)
    (hcard : (orbN0 x).ncard = 7) (hcl : Subgroup.closure (orbN0 x) = A0) :
    x ∈ orbN0 alpha := by
  obtain ⟨h7a, h7b, h21, h28⟩ := ncard_orbN0
  rcases mem_orbN0_of_mem_A0 x hx hx1 with h | h | h | h
  · exact h
  · exfalso
    have h1 := card_closure_orbN0_pi12
    rw [← orbN0_eq_of_mem h, hcl, card_A0] at h1
    norm_num at h1
  · exfalso
    rw [orbN0_eq_of_mem h, h21] at hcard
    norm_num at hcard
  · exfalso
    rw [orbN0_eq_of_mem h, h28] at hcard
    norm_num at hcard

end Orbit

section Nu

variable (F : FusionOut z)

theorem bN_mem (i : Fin 7) : F.b i ∈ Subgroup.normalizer (F.A : Set G) :=
  Subgroup.le_normalizer (b_mem_A F i)

theorem exists_nu : ∃ ν : ↥(Subgroup.normalizer (F.A : Set G)) ≃* ↥N0,
    ((ν ⟨z, z_mem_normalizer F⟩ : ↥N0) : StatedSp 3 (ZMod 2)) = alpha := by
  obtain ⟨ν₀⟩ := nonempty_nu0 F
  set N := Subgroup.normalizer (F.A : Set G) with hN
  set zN : ↥N := ⟨z, z_mem_normalizer F⟩ with hzN
  have hAN : F.A ≤ N := Subgroup.le_normalizer
  have hA2 : IsPGroup 2 ↥(F.A.subgroupOf N) := by
    refine IsPGroup.of_card (n := 6) ?_
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAN).toEquiv, card_A F]
    norm_num
  haveI : (F.A.subgroupOf N).Normal := Subgroup.normal_in_normalizer
  have himgA : (F.A.subgroupOf N).map ν₀.toMonoidHom = A0.subgroupOf N0 := by
    haveI : ((F.A.subgroupOf N).map ν₀.toMonoidHom).Normal :=
      Subgroup.Normal.map inferInstance _ ν₀.surjective
    refine Subgroup.eq_of_le_of_card_ge (le_A0_subgroupOf inferInstance (hA2.map _)) ?_
    rw [Subgroup.card_map_of_injective ν₀.injective,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe A0_le_N0).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAN).toEquiv, card_A F, card_A0]
  have hmemA0 : ∀ x (hx : x ∈ F.A), ((ν₀ ⟨x, hAN hx⟩ : ↥N0) : StatedSp 3 (ZMod 2)) ∈ A0 := by
    intro x hx
    have h : ν₀ ⟨x, hAN hx⟩ ∈ (F.A.subgroupOf N).map ν₀.toMonoidHom := ⟨_, hx, rfl⟩
    rw [himgA] at h
    exact h
  set f : Fin 7 → StatedSp 3 (ZMod 2) := fun i => (ν₀ ⟨F.b i, bN_mem F i⟩ : ↥N0) with hf
  have horb : orbN0 (ν₀ zN : StatedSp 3 (ZMod 2)) = Set.range f := by
    ext w
    constructor
    · rintro ⟨m, hm, rfl⟩
      obtain ⟨n, hn⟩ := ν₀.surjective ⟨m, hm⟩
      obtain ⟨i, hi⟩ := (F.b_orbit ((n : G) * z * (n : G)⁻¹)).mp ⟨n, n.2, rfl⟩
      refine ⟨i, ?_⟩
      have e : (⟨F.b i, bN_mem F i⟩ : ↥N) = n * zN * n⁻¹ := Subtype.ext hi
      simp only [hf, e, map_mul, map_inv, hn, Subgroup.coe_mul, Subgroup.coe_inv]
    · rintro ⟨i, rfl⟩
      obtain ⟨n, hn, hni⟩ := (F.b_orbit (F.b i)).mpr ⟨i, rfl⟩
      refine ⟨(ν₀ ⟨n, hn⟩ : StatedSp 3 (ZMod 2)), (ν₀ ⟨n, hn⟩).2, ?_⟩
      have e : (⟨F.b i, bN_mem F i⟩ : ↥N) = ⟨n, hn⟩ * zN * ⟨n, hn⟩⁻¹ := Subtype.ext hni.symm
      simp only [hf, e, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]
  have hfinj : Function.Injective f := by
    intro i j hij
    have h1 : ν₀ ⟨F.b i, bN_mem F i⟩ = ν₀ ⟨F.b j, bN_mem F j⟩ := Subtype.ext hij
    exact F.b_inj (congrArg Subtype.val (ν₀.injective h1))
  have hcard : (orbN0 (ν₀ zN : StatedSp 3 (ZMod 2))).ncard = 7 := by
    rw [horb, Set.ncard_range_of_injective hfinj, Nat.card_eq_fintype_card, Fintype.card_fin]
  have hcl : Subgroup.closure (orbN0 (ν₀ zN : StatedSp 3 (ZMod 2))) = A0 := by
    rw [horb]
    have hclN : Subgroup.closure (Set.range (fun i => (⟨F.b i, bN_mem F i⟩ : ↥N))) =
        F.A.subgroupOf N := by
      apply Subgroup.map_injective N.subtype_injective
      rw [MonoidHom.map_closure, ← Set.range_comp, Subgroup.subgroupOf_map_subtype,
        inf_eq_left.mpr hAN]
      exact F.b_closure
    have hf' : Set.range f = (N0.subtype.comp ν₀.toMonoidHom) ''
        Set.range (fun i => (⟨F.b i, bN_mem F i⟩ : ↥N)) := by
      rw [← Set.range_comp]
      rfl
    rw [hf', ← MonoidHom.map_closure, hclN, ← Subgroup.map_map, himgA,
      Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr A0_le_N0]
  have hz1 : (ν₀ zN : StatedSp 3 (ZMod 2)) ≠ 1 := by
    intro h
    have h1 : ν₀ zN = 1 := Subtype.ext h
    have h2 : zN = 1 := ν₀.injective (by rw [h1, map_one])
    have h3 : z = 1 := congrArg Subtype.val h2
    have hz2 := F.θ_z
    have : (⟨z, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩ :
        ↥(Subgroup.centralizer ({z} : Set G))) = 1 := Subtype.ext h3
    rw [this, map_one] at hz2
    have h7 := ncard_orbN0.1
    have h1' : orbN0 alpha = {1} := by
      rw [← hz2]
      ext w
      simp only [orbN0, Set.mem_setOf_eq, Set.mem_singleton_iff, OneMemClass.coe_one, mul_one,
        mul_inv_cancel]
      exact ⟨fun ⟨_, _, h⟩ => h.symm, fun h => ⟨1, N0.one_mem, h.symm⟩⟩
    rw [h1', Set.ncard_singleton] at h7
    norm_num at h7
  obtain ⟨m, hm, hmα⟩ := mem_orbN0_alpha_of (hmemA0 z (z_mem_A F)) hz1 hcard hcl
  refine ⟨ν₀.trans (MulAut.conj (⟨m, hm⟩ : ↥N0)⁻¹), ?_⟩
  show ((⟨m, hm⟩ : ↥N0)⁻¹ * ν₀ zN * (⟨m, hm⟩ : ↥N0)⁻¹⁻¹ : StatedSp 3 (ZMod 2)) = alpha
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, inv_inv]
  rw [← hmα]
  group

end Nu

end CFSG.RankThree.PartTwo.Sec19.SolEven.YamakiRec
