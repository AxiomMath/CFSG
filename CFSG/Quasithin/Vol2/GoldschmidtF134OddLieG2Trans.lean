module

public import CFSG.Quasithin.Vol2.GoldschmidtF134OddLieCfg

public section

open CFSG.QuasithinUnique
open scoped commutatorElement

namespace CFSG.Quasithin.H13.NQCore.G2

theorem exists_mulEquiv_map_sylow_eq {X Y : Type*} [Group X] [Group Y] [Finite X] {p : ℕ}
    [Fact p.Prime] (e₀ : X ≃* Y) (S : Sylow p X) (S' : Sylow p Y) :
    ∃ e : X ≃* Y, (S : Subgroup X).map e.toMonoidHom = S' := by
  have : Finite Y := Finite.of_equiv X e₀.toEquiv
  have hsurj : Function.Surjective e₀.toMonoidHom := e₀.surjective
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Y (S.mapSurjective hsurj) S'
  refine ⟨e₀.trans (MulAut.conj g), ?_⟩
  have h : ((g • S.mapSurjective hsurj : Sylow p Y) : Subgroup Y) =
      ((S.mapSurjective hsurj : Sylow p Y) : Subgroup Y).map (MulAut.conj g).toMonoidHom := by
    ext x
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists, Subgroup.mem_map]
    rfl
  rw [← hg, h, Sylow.coe_mapSurjective, Subgroup.map_map]
  rfl

theorem false_of_borel_data {A : Type} [Group A] [Finite A] {p : ℕ} [hp : Fact p.Prime]
    (hp5 : 5 ≤ p) {L P T : Subgroup A} (hcfg : OddCfg p L P T) {C : Type} [Group C]
    (e₀ : C ≃* ↥L) {U B : Subgroup C} (hUp : IsPGroup 2 U) (hUi : ¬ 2 ∣ U.index)
    (hcont : ∀ (a : ℕ) (H : Subgroup C), (a = 2 ∨ a = 3) → U ≤ H →
      Nat.card H = p ^ a * Nat.card U → H ≤ B)
    (hcomm : ∀ x ∈ B, ∀ y ∈ B, x * y * x⁻¹ * y⁻¹ ∈ U)
    (hpow : ∀ α : MulAut C, U.map α.toMonoidHom = U →
      ∃ s : ℕ, ∀ b ∈ B, (α b)⁻¹ * b ^ 2 ^ s ∈ U) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLn := hcfg.normal
  have : Finite C := Finite.of_equiv L e₀.symm.toEquiv
  have hS := hcfg.isSylowTwoOf_inf
  obtain ⟨a, ha, hPa⟩ := hcfg.exists_card
  have hcardsub : ∀ {S : Subgroup A}, S ≤ L → Nat.card (S.subgroupOf L) = Nat.card S :=
    fun h => Nat.card_congr (Subgroup.subgroupOfEquivOfLe h).toEquiv
  obtain ⟨e, he⟩ := exists_mulEquiv_map_sylow_eq e₀ (hUp.toSylow hUi)
    ((hS.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hS.1).symm).toSylow hS.2.2)
  replace he : U.map e.toMonoidHom = (T ⊓ L).subgroupOf L := he
  have he_inj : Function.Injective e.toMonoidHom := e.injective
  have he_surj : Function.Surjective e.toMonoidHom := e.surjective
  have hmemU : ∀ w : L, w ∈ (T ⊓ L).subgroupOf L → e.symm w ∈ U := by
    intro w hw
    rw [← he, Subgroup.mem_map_equiv] at hw
    exact hw
  have hcardU' : Nat.card ((T ⊓ L).subgroupOf L) = Nat.card U := by
    rw [← he, Subgroup.card_map_of_injective he_inj]
  have hcomap : ∀ S : Subgroup L, Nat.card (S.comap e.toMonoidHom) = Nat.card S := by
    intro S
    rw [← Subgroup.card_map_of_injective he_inj,
      Subgroup.map_comap_eq_self_of_surjective he_surj]
  set PC := (P.subgroupOf L).comap e.toMonoidHom with hPC
  set HC := ((P ⊔ T ⊓ L).subgroupOf L).comap e.toMonoidHom with hHC
  have hPHC : PC ≤ HC := fun x hx => by
    change ((e x : L) : A) ∈ P ⊔ T ⊓ L
    exact le_sup_left (α := Subgroup A) hx
  have hPCcard : Nat.card PC = p ^ a := by
    rw [hPC, hcomap, hcardsub hcfg.le, hPa]
  have hUHC : U ≤ HC := fun u hu => by
    have h1 : e u ∈ (T ⊓ L).subgroupOf L := he ▸ Subgroup.mem_map_of_mem e.toMonoidHom hu
    change ((e u : L) : A) ∈ P ⊔ T ⊓ L
    exact le_sup_right (α := Subgroup A) h1
  have hHCcard : Nat.card HC = p ^ a * Nat.card U := by
    rw [hHC, hcomap, hcardsub hcfg.sup_inf_le, hcfg.card_sup_inf hp5, hPa, ← hcardU',
      hcardsub (inf_le_right : T ⊓ L ≤ L)]
  have hHB : HC ≤ B := hcont a HC ha hUHC hHCcard
  have hmemPC : ∀ x : L, (x : A) ∈ P → e.symm x ∈ PC := fun x hx => by
    change ((e (e.symm x) : L) : A) ∈ P
    rw [MulEquiv.apply_symm_apply]
    exact hx
  have hdisj : Disjoint PC U := by
    refine Subgroup.disjoint_of_coprime_natCard ?_
    rw [hPCcard]
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hUp
    rw [hk]
    exact Nat.Coprime.pow _ _ ((Nat.coprime_primes hp.out Nat.prime_two).2 (by omega))
  have hact : ∀ t ∈ T ⊓ Subgroup.normalizer (P : Set A), ∃ s : ℕ, ∀ x ∈ P,
      t * x * t⁻¹ = x ^ 2 ^ s := by
    intro t ht
    set β : MulAut L := MulAut.conjNormal t with hβ
    have hβU : ∀ w : L, w ∈ (T ⊓ L).subgroupOf L → β w ∈ (T ⊓ L).subgroupOf L := by
      intro w hw
      rw [Subgroup.mem_subgroupOf] at hw ⊢
      rw [hβ, MulAut.conjNormal_apply]
      exact ⟨T.mul_mem (T.mul_mem ht.1 hw.1) (T.inv_mem ht.1), hLn.conj_mem _ hw.2 t⟩
    set α : MulAut C := (e.trans β).trans e.symm with hα
    have hαU : U.map α.toMonoidHom = U := by
      refine Subgroup.eq_of_le_of_card_ge ?_ (by rw [Subgroup.card_map_of_injective α.injective])
      rintro _ ⟨z, hz, rfl⟩
      have h1 : e z ∈ (T ⊓ L).subgroupOf L := he ▸ Subgroup.mem_map_of_mem e.toMonoidHom hz
      exact hmemU _ (hβU _ h1)
    obtain ⟨s, hs⟩ := hpow α hαU
    refine ⟨s, fun x hx => ?_⟩
    have hxL : x ∈ L := hcfg.le hx
    have htx : t * x * t⁻¹ ∈ P := (Subgroup.mem_normalizer_iff.1 ht.2 x).1 hx
    have hxC : e.symm ⟨x, hxL⟩ ∈ PC := hmemPC ⟨x, hxL⟩ hx
    have hxB : e.symm ⟨x, hxL⟩ ∈ B := hHB (hPHC hxC)
    have hαx : α (e.symm ⟨x, hxL⟩) = e.symm (β ⟨x, hxL⟩) := by
      rw [hα, MulEquiv.trans_apply, MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
    have hyP : (α (e.symm ⟨x, hxL⟩))⁻¹ * e.symm ⟨x, hxL⟩ ^ 2 ^ s ∈ PC := by
      change ((e ((α (e.symm ⟨x, hxL⟩))⁻¹ * e.symm ⟨x, hxL⟩ ^ 2 ^ s) : L) : A) ∈ P
      rw [map_mul, map_inv, map_pow, hαx, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply,
        Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_pow, hβ, MulAut.conjNormal_apply]
      exact P.mul_mem (P.inv_mem htx) (P.pow_mem hx _)
    have hy1 := Subgroup.disjoint_def.1 hdisj hyP (hs _ hxB)
    have h2 := congrArg e (inv_mul_eq_one.1 hy1)
    rw [hαx, MulEquiv.apply_symm_apply, map_pow, MulEquiv.apply_symm_apply] at h2
    have h3 := congrArg Subtype.val h2
    rwa [hβ, MulAut.conjNormal_apply, Subgroup.coe_pow] at h3
  have hPcomm : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x := by
    intro x hx y hy
    have hxC := hmemPC ⟨x, hcfg.le hx⟩ hx
    have hyC := hmemPC ⟨y, hcfg.le hy⟩ hy
    have h1 := Subgroup.disjoint_def.1 hdisj
      (PC.mul_mem (PC.mul_mem (PC.mul_mem hxC hyC) (PC.inv_mem hxC)) (PC.inv_mem hyC))
      (hcomm _ (hHB (hPHC hxC)) _ (hHB (hPHC hyC)))
    have h2 := congrArg e h1
    simp only [map_mul, map_inv, map_one, MulEquiv.apply_symm_apply] at h2
    have h3 := congrArg Subtype.val h2
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_one] at h3
    calc x * y = x * y * x⁻¹ * y⁻¹ * (y * x) := by group
      _ = y * x := by rw [h3, one_mul]
  obtain ⟨x, hxP, hx1⟩ : ∃ x ∈ P, x ≠ 1 := by
    by_contra hcon
    push Not at hcon
    rw [(Subgroup.eq_bot_iff_forall P).2 hcon, Subgroup.card_bot] at hPa
    have : 1 < p ^ a := Nat.one_lt_pow (by omega) hp.out.one_lt
    omega
  have hxp : orderOf x = p := orderOf_eq_prime (hcfg.exp x hxP) hx1
  have hQP : Subgroup.zpowers x ≤ P := Subgroup.zpowers_le.2 hxP
  have hN : T ⊓ Subgroup.normalizer (P : Set A) ≤
      Subgroup.normalizer (Subgroup.zpowers x : Set A) := by
    have hfwd : ∀ t ∈ T ⊓ Subgroup.normalizer (P : Set A), ∀ y ∈ Subgroup.zpowers x,
        t * y * t⁻¹ ∈ Subgroup.zpowers x := by
      intro t ht y hy
      obtain ⟨s, hs⟩ := hact t ht
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
      rw [← conj_zpow, hs x hxP]
      exact Subgroup.zpow_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers x) _) k
    intro t ht
    rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨hfwd t ht y, fun hy => ?_⟩
    have h := hfwd t⁻¹ ((T ⊓ Subgroup.normalizer (P : Set A)).inv_mem ht) _ hy
    have e1 : t⁻¹ * (t * y * t⁻¹) * t⁻¹⁻¹ = y := by group
    rwa [e1] at h
  have hPP : ⁅P, P⁆ = ⊥ := by
    rw [eq_bot_iff, Subgroup.commutator_le]
    intro u hu v hv
    have h := hPcomm v hv u⁻¹ (P.inv_mem hu)
    rw [Subgroup.mem_bot, commutatorElement_def, mul_assoc u v, h]
    group
  rcases hcfg.irred _ (by rw [hPP]; exact bot_le) hQP hN with h | h
  · rw [hPP] at h
    exact hx1 (Subgroup.mem_bot.1 (h ▸ Subgroup.mem_zpowers x))
  · rw [← h, Nat.card_zpowers, hxp] at hPa
    have h1 : p ^ 1 < p ^ a := Nat.pow_lt_pow_right hp.out.one_lt (by omega)
    rw [pow_one] at h1
    omega

end CFSG.Quasithin.H13.NQCore.G2
