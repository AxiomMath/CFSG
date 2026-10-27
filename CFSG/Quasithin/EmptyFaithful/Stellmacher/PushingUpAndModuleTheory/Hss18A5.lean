module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.Hss18Basic
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.Hss18A5Gen
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.Hss18A5Ind
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.Hss113Core

public section

namespace CFSG.Quasithin.F53Push

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F53Mod Equiv

variable {G : Type} [Group G]

section Rep

variable {H L N : Subgroup G}

@[expose] noncomputable def a5Rep (hs : IsSec H L N) (θ : ↥H →* ↥(alternatingGroup (Fin 5)))
    (hθ : Function.Surjective θ) (hk : θ.ker ≤ (cSecIn H L N).subgroupOf H) :
    ↥(alternatingGroup (Fin 5)) →* MulAut hs.W :=
  MonoidHom.liftOfSurjective θ hθ ⟨hs.conjHom, fun _ hh =>
    hs.conjHom_eq_one fun x hx =>
      ((mem_cSecIn_iff (hs.normL)).mp (Subgroup.mem_subgroupOf.mp (hk hh))).2 x hx⟩

variable (hs : IsSec H L N) (θ : ↥H →* ↥(alternatingGroup (Fin 5)))
  (hθ : Function.Surjective θ) (hk : θ.ker ≤ (cSecIn H L N).subgroupOf H)

theorem a5Rep_apply (h : ↥H) : a5Rep hs θ hθ hk (θ h) = hs.conjHom h := by
  have := MonoidHom.liftOfRightInverse_comp_apply θ (Function.surjInv hθ)
    (Function.rightInverse_surjInv hθ)
    (⟨hs.conjHom, fun h hh => hs.conjHom_eq_one fun x hx =>
      ((mem_cSecIn_iff (hs.normL)).mp (Subgroup.mem_subgroupOf.mp (hk hh))).2 x hx⟩ :
      {g : ↥H →* MulAut hs.W // θ.ker ≤ g.ker}) h
  exact this

theorem a5Rep_proj (h : ↥H) (x : ↥N) :
    a5Rep hs θ hθ hk (θ h) (hs.proj x) = hs.proj (hs.conjN h x) := by
  rw [a5Rep_apply]
  rfl

end Rep

theorem relIndex_le_index_of_finite {α : Type*} [Group α] [Finite α] (H K : Subgroup α) :
    H.relIndex K ≤ H.index := by
  have h1 := Subgroup.relIndex_mul_index (inf_le_right : H ⊓ K ≤ K)
  have h2 : (H ⊓ K).index ≤ H.index * K.index := Subgroup.index_inf_le
  rw [Subgroup.inf_relIndex_right] at h1
  have hK : 0 < K.index := Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero
  have : H.relIndex K * K.index ≤ H.index * K.index := h1 ▸ h2
  exact Nat.le_of_mul_le_mul_right this hK

theorem c5_pow_three : (swap (0 : Fin 5) 1 * swap 1 2) ^ 3 = 1 := by decide +kernel

theorem c5_ne_one : (swap (0 : Fin 5) 1 * swap 1 2) ≠ 1 := by decide +kernel

theorem c5_mem : (swap (0 : Fin 5) 1 * swap 1 2) ∈ alternatingGroup (Fin 5) := by
  rw [Perm.mem_alternatingGroup]; decide

theorem hss18A5_holds (G : Type) [Group G] [Finite G] :
    ∀ X P Z : Subgroup G, PushHyp X P Z → Nonempty (OTwoQuot X ≃* ↥(alternatingGroup (Fin 5))) →
      ¬ thompsonJ P ≤ pCoreOf 2 X → IsNatSecA5 X (zZero X Z) Z := by
  intro X P Z h he hJ
  obtain ⟨e⟩ := he
  obtain ⟨θ, hθ, hker⟩ := exists_hom_of_quot e
  obtain ⟨A, hA, hAQ⟩ := exists_offender hJ
  have hs := isSec_inf_centralizer_oTwoRes h.elemAbelian h.normal
  set K := Z ⊓ Subgroup.centralizer (oTwoRes X : Set G) with hK
  have hk := ker_le_cSecIn h θ hker K
  have : Finite hs.W := by
    have := hs.normal_subgroupOf
    exact (inferInstance : Finite (↥Z ⧸ K.subgroupOf Z))
  set ρ := a5Rep hs θ hθ hk with hρ
  have hsq : ∀ w : hs.W, w * w = 1 := fun w => by
    obtain ⟨x, rfl⟩ := hs.proj_surjective w
    rw [← map_mul, hs.proj_eq_one_iff]
    simpa [pow_two] using hs.sq x x.2
  have hfree : ∀ w : hs.W, (∀ a (ha : a ∈ alternatingGroup (Fin 5)), ρ ⟨a, ha⟩ w = w) →
      w = 1 := fun w hw => by
    obtain ⟨z, rfl⟩ := hs.proj_surjective w
    refine (hs.proj_eq_one_iff z).mpr ?_
    refine mem_inf_centralizer_oTwoRes_of_forall h.elemAbelian z.2 fun x hx => ?_
    have h1 : ρ (θ ⟨x, hx⟩) (hs.proj z) = hs.proj z := hw _ (θ ⟨x, hx⟩).2
    rw [hρ, a5Rep_proj hs θ hθ hk ⟨x, hx⟩ z] at h1
    exact (hs.proj_eq_proj_iff _ _).mp h1.symm
  have hmov : ∃ w : hs.W, w ≠ 1 := by
    set c : ↥(alternatingGroup (Fin 5)) := ⟨_, c5_mem⟩ with hc
    have hc3 : orderOf c = 3 := orderOf_eq_prime
      (Subtype.ext (by simpa using c5_pow_three)) (fun h1 => c5_ne_one (congrArg Subtype.val h1))
    obtain ⟨d, hdL, hdX, k, hdk⟩ := exists_odd_elt (X := X) θ hθ (c := c)
    obtain ⟨hodd, hne⟩ := odd_orderOf_pow_two_pow (c := c) (by rw [hc3]; decide) k
    obtain ⟨z, hz, hzK⟩ := exists_moved h θ hker hdL hdX (by rw [hdk]; exact hodd)
      (by rw [hdk]; exact fun h1 => (by
        have := hne h1
        exact c5_ne_one (congrArg Subtype.val this)))
    refine ⟨hs.proj ⟨z, hz⟩, fun h1 => hzK ?_⟩
    have h2 : ρ (θ ⟨d, hdX⟩) (hs.proj ⟨z, hz⟩) = hs.proj ⟨z, hz⟩ := by
      rw [h1, map_one]
    rw [hρ, a5Rep_proj hs θ hθ hk ⟨d, hdX⟩ ⟨z, hz⟩] at h2
    exact (hs.proj_eq_proj_iff _ _).mp h2.symm
  obtain ⟨w₀, hw₀⟩ := hmov
  obtain ⟨Q, hQcl, hfixQ, ι, hinj, hequiv⟩ := exists_inj_model ρ hsq hfree hw₀
  have hAX : A ≤ X := hA.1.trans h.le_self
  set θ' : ↥X →* Perm (Fin 5) := (alternatingGroup (Fin 5)).subtype.comp θ with hθ'
  have hker' : ∀ x : ↥X, θ' x = 1 ↔ (x : G) ∈ pCoreOf 2 X := fun x => by
    rw [← hker x, hθ', MonoidHom.comp_apply]
    exact OneMemClass.coe_eq_one
  set B : Subgroup (Perm (Fin 5)) := (A.subgroupOf X).map θ' with hB
  have hBcard : Nat.card B = (A ⊓ pCoreOf 2 X).relIndex A := by
    rw [hB, card_map_subgroupOf_eq_relIndex θ' hker' hAX, Subgroup.inf_relIndex_left]
  have hBne : B ≠ ⊥ := by
    intro h1
    apply hAQ
    intro y hy
    have : θ' ⟨y, hAX hy⟩ ∈ B := ⟨⟨y, hAX hy⟩, hy, rfl⟩
    rw [h1, Subgroup.mem_bot] at this
    exact (hker' _).mp this
  have hBexp : ∀ x ∈ B, x * x = 1 := by
    rintro _ ⟨y, hy, rfl⟩
    rw [← map_mul]
    have : y * y = 1 := Subtype.ext (by simpa [pow_two] using hA.2.1.2 y hy)
    rw [this, map_one]
  have hBA : B ≤ alternatingGroup (Fin 5) := by
    rintro _ ⟨y, -, rfl⟩
    exact (θ y).2
  have hoffV : (fixA5 ρ B).index ≤ (A ⊓ pCoreOf 2 X).relIndex A := by
    refine le_trans ?_ (offender_count h hA)
    let P : Subgroup ↥Z := (Z ⊓ Subgroup.centralizer (A : Set G)).subgroupOf Z
    have hPle : P.map hs.proj ≤ fixA5 ρ B := by
      rintro _ ⟨x, hx, rfl⟩ b ⟨y, hy, rfl⟩ hbA
      show ρ (θ ⟨y, hAX hy⟩) (hs.proj x) = hs.proj x
      rw [hρ, a5Rep_proj hs θ hθ hk ⟨y, _⟩ x]
      congr 1
      apply Subtype.ext
      show (y : G) * x * (y : G)⁻¹ = x
      rw [mul_inv_eq_iff_eq_mul]
      exact Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hx).2 y
        (Subgroup.mem_subgroupOf.mp hy)
    have h1 := Subgroup.index_dvd_of_le hPle
    have h2 : (P.map hs.proj).index ∣ P.index :=
      Subgroup.index_map_dvd (H := P) hs.proj_surjective
    exact Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero) (h1.trans h2)
  have hoffQ : (fixW Q B).index ≤ Nat.card B := by
    have hfq : fixW Q B = (fixA5 ρ B).comap ι := by
      ext u
      rw [Subgroup.mem_comap]
      constructor
      · intro hu b hb hbA
        have := hequiv b hbA u
        rw [hu b hb] at this
        exact this.symm
      · intro hu b hb
        apply hinj
        rw [hequiv b (hBA hb) u]
        exact hu b hb (hBA hb)
    rw [hfq, Subgroup.index_comap]
    exact (relIndex_le_index_of_finite _ _).trans (hoffV.trans hBcard.ge)
  have hQnt : ∃ w : Q.W, w ≠ 1 := by
    rcases hQcl with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
    · exact (Model.IsIrred.of_iso e.symm orth_isIrred).1
    · exact (Model.IsIrred.of_iso e.symm nat_isIrred).1
  obtain ⟨hidx, hcases⟩ := offender_dichotomy Q hQnt hfixQ hBne hBexp hoffQ
  have hnat : Nonempty (Q.Iso nat) ∧ Nat.card B = 4 := by
    rcases hcases with ⟨-, ⟨t, ht, hBt⟩ | ⟨-, hnA⟩⟩ | ⟨he', hc4, -⟩
    · exfalso
      have htB : t ∈ B := hBt ▸ Subgroup.mem_zpowers t
      have := Perm.mem_alternatingGroup.mp (hBA htB)
      rw [ht.sign_eq] at this
      exact absurd this (by decide)
    · exact absurd hBA hnA
    · exact ⟨he', hc4⟩
  obtain ⟨⟨e'⟩, hB4⟩ := hnat
  have hQcard : Nat.card Q.W = 16 := by
    rw [Nat.card_congr e'.toMulEquiv.toEquiv]
    exact card_nat
  have hVle : Nat.card hs.W ≤ 16 := by
    have h1 := card_le_index_fixA5_sq ρ hfree hBA hBexp hB4
    have h2 : (fixA5 ρ B).index ≤ 4 := by rw [← hB4]; exact hoffV.trans hBcard.ge
    calc Nat.card hs.W ≤ (fixA5 ρ B).index ^ 2 := h1
      _ ≤ 4 ^ 2 := Nat.pow_le_pow_left h2 2
      _ = 16 := by norm_num
  have hbij : Function.Bijective ι := hinj.bijective_of_nat_card_le (by omega)
  let Φ : nat.W ≃* hs.W := e'.symm.toMulEquiv.trans (MulEquiv.ofBijective ι hbij)
  have hΦ : ∀ a (ha : a ∈ alternatingGroup (Fin 5)) (u : nat.W),
      Φ (nat.act a u) = ρ ⟨a, ha⟩ (Φ u) := fun a ha u => by
    show ι (e'.symm.toMulEquiv (nat.act a u)) = ρ ⟨a, ha⟩ (ι (e'.symm.toMulEquiv u))
    rw [e'.symm.map_act, hequiv a ha]
  rw [zZero_eq]
  have hN := hs.normal_subgroupOf
  refine ⟨hN, θ, (Φ.toMonoidHom : nat.W →* ↥Z ⧸ K.subgroupOf Z), hθ, ?_,
    Φ.surjective, Φ.injective, ?_⟩
  · refine le_antisymm hk (fun f hf => ?_)
    have hf' := (mem_cSecIn_iff hs.normL).mp (Subgroup.mem_subgroupOf.mp hf)
    have h1 : ρ (θ f) = 1 := by
      rw [hρ, a5Rep_apply hs θ hθ hk f]
      exact hs.conjHom_eq_one hf'.2
    have h2 : nat.act (θ f : Perm (Fin 5)) = nat.act 1 := by
      ext u
      apply Φ.injective
      have := hΦ (θ f : Perm (Fin 5)) (θ f).2 u
      rw [h1] at this
      simpa using this
    have h3 := nat_faithful h2
    exact Subtype.ext h3
  · intro k u x hux
    refine ⟨hs.conj_mem_N k x, ?_⟩
    have h1 : Φ u = hs.proj x := hux
    show Φ (nat.act (θ k : Perm (Fin 5)) u) = _
    rw [hΦ _ (θ k).2, h1, hρ]
    exact a5Rep_proj hs θ hθ hk k x

end CFSG.Quasithin.F53Push
