module

public import CFSG.ClassicalInvolution.Sp62Rec.Recognition
public import CFSG.RankThree.PartTwo.Sec19.SimsSolEvenYamakiNu
import CFSG.ClassicalInvolution.Solomon73.YamakiLemma20
import CFSG.ClassicalInvolution.Sp62Rec.ModelCR1NA
public import CFSG.RankThree.PartTwo.Sec19.SimsSolEvenYamakiDefs

public section

namespace CFSG.RankThree.PartTwo.Sec19.SolEven.YamakiRec

open CFSG.ClassicalInvolution.Solomon73 CFSG.ClassicalInvolution.Solomon73.Yamaki
open CFSG.ClassicalInvolution.Sp62Rec CFSG.ClassicalInvolution.Q3.AE CFSG.Open
open CFSG.RankThree.PartTwo.Sec19.SolEven.Yamaki (FusionOut FusionOutStatement)

variable
  {G : Type} [Group G] [Finite G] {z : G}

section Amalgam

variable (F : FusionOut z)

theorem theta_symm_alpha :
    ((F.θ.symm ⟨alpha, S0_le_Hhat alpha_mem_S0⟩ : ↥(Subgroup.centralizer ({z} : Set G))) : G) =
      z := by
  have h : F.θ.symm ⟨alpha, S0_le_Hhat alpha_mem_S0⟩ =
      ⟨z, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩ := by
    rw [MulEquiv.symm_apply_eq]
    exact Subtype.ext F.θ_z.symm
  rw [h]

theorem mem_normalizer_iff_theta (x : G) (hx : x ∈ Subgroup.centralizer ({z} : Set G)) :
    x ∈ Subgroup.normalizer (F.A : Set G) ↔ (F.θ ⟨x, hx⟩ : StatedSp 3 (ZMod 2)) ∈ X0 := by
  rw [X0_eq_normalizer_inf_Hhat, Subgroup.mem_inf]
  have key : ∀ c (hc : c ∈ Subgroup.centralizer ({z} : Set G)) a
      (ha : a ∈ Subgroup.centralizer ({z} : Set G)), c * a * c⁻¹ ∈ F.A ↔
      (F.θ ⟨c, hc⟩ : StatedSp 3 (ZMod 2)) * (F.θ ⟨a, ha⟩) *
        (F.θ ⟨c, hc⟩ : StatedSp 3 (ZMod 2))⁻¹ ∈ A0 := by
    intro c hc a ha
    have hcaC : c * a * c⁻¹ ∈ Subgroup.centralizer ({z} : Set G) :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hc ha) (Subgroup.inv_mem _ hc)
    rw [F.θ_A _ hcaC]
    have e : (⟨c * a * c⁻¹, hcaC⟩ : ↥(Subgroup.centralizer ({z} : Set G))) =
        ⟨c, hc⟩ * ⟨a, ha⟩ * ⟨c, hc⟩⁻¹ := rfl
    rw [e, map_mul, map_mul, map_inv]
    rfl
  have haH : x⁻¹ ∈ Subgroup.centralizer ({z} : Set G) := Subgroup.inv_mem _ hx
  have hθinv : (F.θ ⟨x⁻¹, haH⟩ : StatedSp 3 (ZMod 2)) =
      (F.θ ⟨x, hx⟩ : StatedSp 3 (ZMod 2))⁻¹ := by
    have e : (⟨x⁻¹, haH⟩ : ↥(Subgroup.centralizer ({z} : Set G))) = (⟨x, hx⟩)⁻¹ := rfl
    rw [e, map_inv]
    rfl
  constructor
  · intro hxN
    refine ⟨?_, (F.θ ⟨x, hx⟩).2⟩
    rw [Subgroup.mem_normalizer_iff]
    intro a
    constructor
    · intro ha
      set a' := F.θ.symm ⟨a, A0_le_Hhat ha⟩
      have ha' : (a' : G) ∈ F.A := (F.θ_A _ a'.2).mpr (by
        rw [Subtype.coe_eta, MulEquiv.apply_symm_apply]; exact ha)
      have h1 := (key x hx a' a'.2).mp ((Subgroup.mem_normalizer_iff.mp hxN _).mp ha')
      rwa [Subtype.coe_eta, MulEquiv.apply_symm_apply] at h1
    · intro ha
      set a' := F.θ.symm ⟨_, A0_le_Hhat ha⟩
      have ha' : (a' : G) ∈ F.A := (F.θ_A _ a'.2).mpr (by
        rw [Subtype.coe_eta, MulEquiv.apply_symm_apply]; exact ha)
      have h2 := (key x⁻¹ haH a' a'.2).mp ((Subgroup.mem_normalizer_iff.mp
        (Subgroup.inv_mem _ hxN) _).mp ha')
      rw [Subtype.coe_eta, MulEquiv.apply_symm_apply, hθinv, inv_inv] at h2
      simpa [mul_assoc] using h2
  · rintro ⟨hθN, -⟩
    rw [Subgroup.mem_normalizer_iff]
    intro a
    constructor
    · intro ha
      exact (key x hx a (F.A_le ha)).mpr ((Subgroup.mem_normalizer_iff.mp hθN _).mp
        ((F.θ_A a (F.A_le ha)).mp ha))
    · intro ha
      have hxaC : x * a * x⁻¹ ∈ Subgroup.centralizer ({z} : Set G) := F.A_le ha
      have haC : a ∈ Subgroup.centralizer ({z} : Set G) := by
        have := Subgroup.mul_mem _ (Subgroup.mul_mem _ haH hxaC) hx
        simpa [mul_assoc] using this
      exact (F.θ_A a haC).mpr ((Subgroup.mem_normalizer_iff.mp hθN _).mpr ((key x hx a haC).mp ha))

theorem mem_centralizer_iff_nu (ν : ↥(Subgroup.normalizer (F.A : Set G)) ≃* ↥N0)
    (hνz : ((ν ⟨z, z_mem_normalizer F⟩ : ↥N0) : StatedSp 3 (ZMod 2)) = alpha)
    (x : G) (hx : x ∈ Subgroup.normalizer (F.A : Set G)) :
    x ∈ Subgroup.centralizer ({z} : Set G) ↔ (ν ⟨x, hx⟩ : StatedSp 3 (ZMod 2)) ∈ X0 := by
  rw [X0_eq_centralizer_inf_N0, Subgroup.mem_centralizer_singleton_iff]
  have hN := (ν ⟨x, hx⟩).2
  constructor
  · intro h
    refine ⟨Subgroup.mem_centralizer_singleton_iff.mpr ?_, hN⟩
    have e : (⟨x, hx⟩ : ↥(Subgroup.normalizer (F.A : Set G))) * ⟨z, z_mem_normalizer F⟩ =
        ⟨z, z_mem_normalizer F⟩ * ⟨x, hx⟩ := Subtype.ext h
    have := congrArg (fun y => ((ν y : ↥N0) : StatedSp 3 (ZMod 2))) e
    simp only [map_mul, Subgroup.coe_mul, hνz] at this
    exact this
  · rintro ⟨h, -⟩
    have h' := Subgroup.mem_centralizer_singleton_iff.mp h
    rw [← hνz] at h'
    have e : ν (⟨x, hx⟩ * ⟨z, z_mem_normalizer F⟩) = ν (⟨z, z_mem_normalizer F⟩ * ⟨x, hx⟩) := by
      apply Subtype.ext
      simp only [map_mul, Subgroup.coe_mul]
      exact h'
    exact congrArg Subtype.val (ν.injective e)

end Amalgam

section Gen

variable (F : FusionOut z)

theorem z_mem_T : z ∈ (F.T : Subgroup G) :=
  (F.θ_T z _).mpr (F.θ_z ▸ alpha_mem_S0)

theorem z_comm_T : ∀ t ∈ (F.T : Subgroup G), t * z = z * t := by
  intro t ht
  have htC := F.T_le ht
  have h1 := commute_alpha ((F.θ_T t htC).mp ht)
  rw [← F.θ_z] at h1
  have e : F.θ (⟨t, htC⟩ * ⟨z, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩) =
      F.θ (⟨z, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩ * ⟨t, htC⟩) := by
    apply Subtype.ext
    simp only [map_mul, Subgroup.coe_mul]
    exact h1
  exact congrArg Subtype.val (F.θ.injective e)

theorem normalizer_T_le : Subgroup.normalizer ((F.T : Subgroup G) : Set G) ≤
    Subgroup.centralizer ({z} : Set G) := by
  intro n hn
  have φ := mulEquivS0OfLe S0_le_Hhat F.θ F.T_le F.θ_T
  have hzT := z_mem_T F
  have hyT : n * z * n⁻¹ ∈ (F.T : Subgroup G) := (Subgroup.mem_normalizer_iff.mp hn z).mp hzT
  have hy : ∀ t ∈ (F.T : Subgroup G), t * (n * z * n⁻¹) = (n * z * n⁻¹) * t := by
    intro t ht
    have ht' : n⁻¹ * t * n ∈ (F.T : Subgroup G) := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hn) t).mp ht
      simpa using this
    have h1 := z_comm_T F _ ht'
    calc t * (n * z * n⁻¹) = n * ((n⁻¹ * t * n) * z) * n⁻¹ := by group
      _ = n * (z * (n⁻¹ * t * n)) * n⁻¹ := by rw [h1]
      _ = n * z * n⁻¹ * t := by group
  have heq := eq_of_isConj_of_mem_center F.T φ hzT (z_comm_T F) hyT hy
    (isConj_iff.mpr ⟨n, rfl⟩)
  rw [Subgroup.mem_centralizer_singleton_iff]
  calc n * z = n * z * n⁻¹ * n := by group
    _ = z * n := by rw [← heq]

private theorem isSylowTwoOf_T : QuasithinUnique.IsSylowTwoOf (F.T : Subgroup G) ⊤ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨le_top, F.T.isPGroup', ?_⟩
  change ¬ 2 ∣ (F.T : Subgroup G).relIndex ⊤
  rw [Subgroup.relIndex_top_right]
  exact Sylow.not_dvd_index F.T

private theorem exists_conj_mem_T {K : Subgroup G} (hTK : (F.T : Subgroup G) ≤ K) {x : G}
    (hxK : x ∈ K) (hx : orderOf x = 2) : ∃ g ∈ K, g * x * g⁻¹ ∈ (F.T : Subgroup G) := by
  have hT := QuasithinUnique.isSylowTwoOf_of_le (isSylowTwoOf_T F) hTK
  have hzK : Subgroup.zpowers x ≤ K := (Subgroup.zpowers_le).mpr hxK
  have hz2 : IsPGroup 2 ↥(Subgroup.zpowers x) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, hx, pow_one]
  obtain ⟨S', hxS', hS'⟩ := QuasithinUnique.exists_isSylowTwoOf_of_le hzK hz2
  obtain ⟨h, hhK, hS'eq⟩ := hT.exists_conj hS'
  have hx' : x ∈ S' := hxS' (Subgroup.mem_zpowers x)
  rw [hS'eq] at hx'
  obtain ⟨t, ht, hth⟩ := hx'
  refine ⟨h⁻¹, K.inv_mem hhK, ?_⟩
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hth
  rw [← hth]
  have e : h⁻¹ * (h * t * h⁻¹) * h⁻¹⁻¹ = t := by group
  rw [e]
  exact ht

theorem centralizer_le_sup (x : G)
    (hxK : x ∈ Subgroup.normalizer (F.A : Set G) ⊔ Subgroup.centralizer ({z} : Set G))
    (hx : orderOf x = 2) : Subgroup.centralizer ({x} : Set G) ≤
      Subgroup.normalizer (F.A : Set G) ⊔ Subgroup.centralizer ({z} : Set G) := by
  set K := Subgroup.normalizer (F.A : Set G) ⊔ Subgroup.centralizer ({z} : Set G) with hK
  have hCK : Subgroup.centralizer ({z} : Set G) ≤ K := le_sup_right
  obtain ⟨g, hgK, hgT⟩ := exists_conj_mem_T F (F.T_le.trans hCK) hxK hx
  have hconj : ∀ (u v : G), orderOf (u * v * u⁻¹) = orderOf v := fun u v => by
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
  have ht2 : orderOf (g * x * g⁻¹) = 2 := by rw [hconj, hx]
  obtain ⟨c, hc, hca⟩ := F.conj_A _ hgT ht2
  set a := c * (g * x * g⁻¹) * c⁻¹ with ha
  have ha1 : a ≠ 1 := by
    intro h1
    have h2 : orderOf a = 2 := by rw [ha, hconj]; exact ht2
    rw [h1, orderOf_one] at h2
    exact absurd h2 (by norm_num)
  have hCa := F.cent_le a hca ha1
  have hcgK : c * g ∈ K := K.mul_mem (hCK hc) hgK
  intro y hy
  have hy' : (c * g) * y * (c * g)⁻¹ ∈ Subgroup.centralizer ({a} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff] at hy ⊢
    rw [ha]
    calc c * g * y * (c * g)⁻¹ * (c * (g * x * g⁻¹) * c⁻¹) = c * g * (y * x) * (c * g)⁻¹ := by
          group
      _ = c * g * (x * y) * (c * g)⁻¹ := by rw [hy]
      _ = c * (g * x * g⁻¹) * c⁻¹ * (c * g * y * (c * g)⁻¹) := by group
  have h1 := hCa hy'
  have := K.mul_mem (K.mul_mem (K.inv_mem hcgK) h1) hcgK
  simpa [mul_assoc] using this

theorem closure_involutions_sup (ν : ↥(Subgroup.normalizer (F.A : Set G)) ≃* ↥N0) :
    Subgroup.closure {x | x ∈ Subgroup.normalizer (F.A : Set G) ⊔
        Subgroup.centralizer ({z} : Set G) ∧ orderOf x = 2} =
      Subgroup.normalizer (F.A : Set G) ⊔ Subgroup.centralizer ({z} : Set G) := by
  set K := Subgroup.normalizer (F.A : Set G) ⊔ Subgroup.centralizer ({z} : Set G) with hK
  set I := Subgroup.closure {x | x ∈ K ∧ orderOf x = 2} with hI
  refine le_antisymm ((Subgroup.closure_le _).mpr fun x hx => hx.1) (sup_le ?_ ?_)
  ·
    have key : ∀ m ∈ N0, ∀ hm : m ∈ N0, ((ν.symm ⟨m, hm⟩ : ↥(Subgroup.normalizer (F.A : Set G))) :
        G) ∈ I := by
      intro m hm0
      induction hm0 using Subgroup.closure_induction with
      | mem y hy =>
        intro hm
        obtain ⟨i, -, rfl⟩ := hy
        set y' := ν.symm ⟨yamakiSp i, hm⟩
        have hsq : (y' : G) * y' = 1 := by
          have h1 : ν.symm (⟨yamakiSp i, hm⟩ * ⟨yamakiSp i, hm⟩) = 1 := by
            have : (⟨yamakiSp i, hm⟩ * ⟨yamakiSp i, hm⟩ : ↥N0) = 1 :=
              Subtype.ext (yamakiSp_mul_self i)
            rw [this, map_one]
          rw [map_mul] at h1
          exact congrArg Subtype.val h1
        by_cases h1 : (y' : G) = 1
        · rw [h1]; exact I.one_mem
        · refine Subgroup.subset_closure
            ⟨(le_sup_left : Subgroup.normalizer (F.A : Set G) ≤ K) y'.2, ?_⟩
          exact orderOf_eq_prime (by rw [sq]; exact hsq) h1
      | one =>
        intro hm
        have e : (⟨1, hm⟩ : ↥N0) = 1 := rfl
        rw [e, map_one]
        exact I.one_mem
      | mul a b ha hb iha ihb =>
        intro hm
        have e : (⟨a * b, hm⟩ : ↥N0) = ⟨a, ha⟩ * ⟨b, hb⟩ := rfl
        rw [e, map_mul, Subgroup.coe_mul]
        exact I.mul_mem (iha ha) (ihb hb)
      | inv a ha iha =>
        intro hm
        have e : (⟨a⁻¹, hm⟩ : ↥N0) = (⟨a, ha⟩)⁻¹ := rfl
        rw [e, map_inv, Subgroup.coe_inv]
        exact I.inv_mem (iha ha)
    intro n hn
    have h := key _ (ν ⟨n, hn⟩).2 (ν ⟨n, hn⟩).2
    rwa [Subtype.coe_eta, MulEquiv.symm_apply_apply] at h
  · rw [← F.gen_inv]
    exact Subgroup.closure_mono fun x hx =>
      ⟨(le_sup_right : Subgroup.centralizer ({z} : Set G) ≤ K) hx.1, hx.2⟩

theorem sup_eq_top (ν : ↥(Subgroup.normalizer (F.A : Set G)) ≃* ↥N0) (hz : orderOf z = 2) :
    Subgroup.normalizer (F.A : Set G) ⊔ Subgroup.centralizer ({z} : Set G) = ⊤ := by
  set K := Subgroup.normalizer (F.A : Set G) ⊔ Subgroup.centralizer ({z} : Set G) with hK
  have hCK : Subgroup.centralizer ({z} : Set G) ≤ K := le_sup_right
  set p3 : G := ((F.θ.symm ⟨pi3, S0_le_Hhat pi3_mem_S0⟩ :
    ↥(Subgroup.centralizer ({z} : Set G))) : G) with hp3
  have hp3K : p3 ∈ K := hCK (F.θ.symm ⟨pi3, S0_le_Hhat pi3_mem_S0⟩).2
  have hp3o : orderOf p3 = 2 := by
    rw [hp3, Subgroup.orderOf_coe, MulEquiv.orderOf_eq, Subgroup.orderOf_mk]
    refine orderOf_eq_prime (by rw [sq]; exact isE64_A0.2.1 _ pi3_mem_A0) ?_
    intro h
    apply alpha_ne_pi12
    apply Subtype.ext
    show alpha = pi12
    have h2 : alpha * pi12 = 1 := h
    have h44 : pi12 * pi12 = 1 := yamakiSp_mul_self 4
    calc alpha = alpha * pi12 * pi12 := by rw [mul_assoc, h44, mul_one]
      _ = pi12 := by rw [h2, one_mul]
  have hnc : ¬ IsConj z p3 := by
    have h := not_isConj_symm_alpha_pi3 F.T S0_le_Hhat F.θ F.T_le F.θ_T
    rwa [theta_symm_alpha F] at h
  exact eq_top_of_centralizer_le (centralizer_le_sup F) (closure_involutions_sup F ν) F.T
    (F.T_le.trans hCK) ((normalizer_T_le F).trans hCK)
    (hCK (Subgroup.mem_centralizer_singleton_iff.mpr rfl)) hp3K hz hp3o hnc

end Gen

theorem yamakiSp62CharTwo_of_fusionOut
    (hF : FusionOutStatement) : YamakiSp62CharTwo := by
  intro G _ _ hs hnab hchar S z hz hzS hzc he
  obtain ⟨F⟩ := hF G hs hnab hchar S z hz hzS hzc he
  obtain ⟨ν, hνz⟩ := exists_nu F
  have hC : Subgroup.centralizer
      {((F.θ.symm ⟨alpha, S0_le_Hhat alpha_mem_S0⟩ : ↥(Subgroup.centralizer ({z} : Set G))) : G)}
      ≤ Subgroup.centralizer ({z} : Set G) := by
    rw [theta_symm_alpha F]
  exact lieModel_of_amalgam ν F.θ (mem_centralizer_iff_nu F ν hνz) (mem_normalizer_iff_theta F)
    (not_isConj_hhat_symm_pi12_pi3 F.T F.θ F.T_le F.θ_T) hC (sup_eq_top F ν hz)

end CFSG.RankThree.PartTwo.Sec19.SolEven.YamakiRec
