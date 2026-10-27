module

public import CFSG.RankThree.PartOne.U5K.Facts
import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.RankThree.PartOne.U5K

open CFSG
open CFSG.Assembly.RankThreeEven (projSU)

section Aux

variable {G : Type} [Group G] {Â : Type} [Group Â] {N : Subgroup G} {ρ : ↥N →* Â}

theorem map_conj_mk {k s : G} (hk : k ∈ N) (hs : s ∈ N) (h : k * s * k⁻¹ ∈ N) :
    ρ ⟨k * s * k⁻¹, h⟩ = ρ ⟨k, hk⟩ * ρ ⟨s, hs⟩ * (ρ ⟨k, hk⟩)⁻¹ := by
  have : (⟨k * s * k⁻¹, h⟩ : ↥N) = ⟨k, hk⟩ * ⟨s, hs⟩ * ⟨k, hk⟩⁻¹ := rfl
  rw [this, map_mul, map_mul, map_inv]

theorem map_mem_normalizer_rm {R : Subgroup G} {y : G} (hyN : y ∈ N)
    (hy : y ∈ Subgroup.normalizer (R : Set G)) :
    ρ ⟨y, hyN⟩ ∈ Subgroup.normalizer (rm N ρ R : Set Â) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  have hy' := Subgroup.mem_normalizer_iff.1 hy
  constructor
  · intro hh
    obtain ⟨r, hrN, hrR, rfl⟩ := mem_rm.1 hh
    have hmem : y * r * y⁻¹ ∈ N := N.mul_mem (N.mul_mem hyN hrN) (N.inv_mem hyN)
    refine mem_rm.2 ⟨y * r * y⁻¹, hmem, (hy' r).1 hrR, ?_⟩
    exact map_conj_mk hyN hrN hmem
  · intro hh
    obtain ⟨r, hrN, hrR, hr⟩ := mem_rm.1 hh
    have hmem : y⁻¹ * r * y ∈ N := N.mul_mem (N.mul_mem (N.inv_mem hyN) hrN) hyN
    refine mem_rm.2 ⟨y⁻¹ * r * y, hmem, ?_, ?_⟩
    · have := (hy' (y⁻¹ * r * y)).2 (by simpa [mul_assoc] using hrR)
      exact this
    · have h1 : ρ ⟨y⁻¹ * r * y, hmem⟩ = (ρ ⟨y, hyN⟩)⁻¹ * ρ ⟨r, hrN⟩ * ρ ⟨y, hyN⟩ := by
        have : (⟨y⁻¹ * r * y, hmem⟩ : ↥N) = ⟨y, hyN⟩⁻¹ * ⟨r, hrN⟩ * ⟨y, hyN⟩ := rfl
        rw [this, map_mul, map_mul, map_inv]
      rw [h1, hr]
      group

theorem rm_le_normalizer {S K : Subgroup G} (hKS : K ≤ Subgroup.normalizer (S : Set G)) :
    rm N ρ K ≤ Subgroup.normalizer (rm N ρ S : Set Â) := by
  intro a ha
  obtain ⟨k, hkN, hkK, rfl⟩ := mem_rm.1 ha
  exact map_mem_normalizer_rm hkN (hKS hkK)

theorem le_of_rm_le_rm {T R K : Subgroup G} (hRT : R ≤ T) (hKT : K ≤ T) (hTN : T ≤ N)
    (hinj : ∀ t ∈ T, ∀ ht : t ∈ N, ρ ⟨t, ht⟩ = 1 → t = 1) (h : rm N ρ R ≤ rm N ρ K) :
    R ≤ K := by
  intro r hr
  have hrN : r ∈ N := hTN (hRT hr)
  obtain ⟨k, hkN, hkK, hk⟩ := mem_rm.1 (h (mem_rm.2 ⟨r, hrN, hr, rfl⟩))
  have hkr : k⁻¹ * r ∈ T := T.mul_mem (T.inv_mem (hKT hkK)) (hRT hr)
  have h1 : k⁻¹ * r = 1 := hinj (k⁻¹ * r) hkr (N.mul_mem (N.inv_mem hkN) hrN) (by
    show ρ (⟨k, hkN⟩⁻¹ * ⟨r, hrN⟩) = 1
    rw [map_mul, map_inv, hk, inv_mul_cancel])
  have : r = k := (inv_mul_eq_one.1 h1).symm
  rw [this]
  exact hkK

theorem isElementaryAbelian_of_forall' {p : ℕ} {X : Subgroup Â}
    (hc : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x) (hp : ∀ x ∈ X, x ^ p = 1) :
    IsElementaryAbelian p X := CFSG.IsElementaryAbelian.of_forall hc hp

theorem isElementaryAbelian_rm {p : ℕ} {B : Subgroup G} (hB : IsElementaryAbelian p B) :
    IsElementaryAbelian p ↥(rm N ρ B) := by
  have hcomm : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hB.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hpow : ∀ x ∈ B, x ^ p = 1 := fun x hx => elemPow_eq_one_of_isElementaryAbelian x hx
  refine isElementaryAbelian_of_forall' (fun x hx y hy => ?_) (fun x hx => ?_)
  · obtain ⟨b, hbN, hbB, rfl⟩ := mem_rm.1 hx
    obtain ⟨b', hbN', hbB', rfl⟩ := mem_rm.1 hy
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hcomm b hbB b' hbB')
  · obtain ⟨b, hbN, hbB, rfl⟩ := mem_rm.1 hx
    rw [← map_pow]
    have : (⟨b, hbN⟩ : ↥N) ^ p = 1 := Subtype.ext (hpow b hbB)
    rw [this, map_one]

theorem card_rm [Finite G] {K : Subgroup G} (hKN : K ≤ N)
    (hinj : Function.Injective (ρ.comp (K.subgroupOf N).subtype)) :
    Nat.card (rm N ρ K) = Nat.card K := by
  unfold rm
  rw [← Nat.card_congr (equivMapOfInjOn ρ hinj).toEquiv]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKN).toEquiv

end Aux

variable {G : Type} [Group G] [Finite G]

theorem faithful_pure (hM : U5Model) {f p : ℕ} (hf : 1 ≤ f) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpf : p ∣ 2 ^ f + 1) {I E T B : Subgroup G} (e : ↥I ⧸ Subgroup.center ↥I ≃* projSU 5 2 f)
    (hT : IsSylowOf 2 T (Subgroup.normalizer (I : Set G)))
    (hodd : ¬ 2 ∣ Nat.card (U5Act I e).ker) (hodp : ¬ p ∣ Nat.card (U5Act I e).ker)
    (hEN : E ≤ Subgroup.normalizer (I : Set G))
    (hEinn : ∀ x (hx : x ∈ Subgroup.normalizer (I : Set G)), x ∈ E →
      U5Act I e ⟨x, hx⟩ ∈ U5Inndiag f)
    (hBE : B ≤ E) (hBX : B ≤ (I ⊔ E) ⊓ Subgroup.normalizer (pushingUpS T : Set G))
    (hBel : IsElementaryAbelian p B) (hBcard : Nat.card B = p ^ 2) :
    ∃ b ∈ B, b ≠ 1 ∧ b ∈ Subgroup.centralizer (zOf (pushingUpS T) : Set G) ∧
      ∀ R : Subgroup G, R ≤ pushingUpS T →
        (I ⊔ E) ⊓ Subgroup.normalizer (pushingUpS T : Set G) ≤ Subgroup.normalizer (R : Set G) →
        R ≠ pushingUpS T → b ∈ Subgroup.centralizer (R : Set G) := by
  classical
  have F := u5Facts hM hf hp hp5 hpf e hT hodd
  have hTN : T ≤ Subgroup.normalizer (I : Set G) := hT.1
  have hIN : I ≤ Subgroup.normalizer (I : Set G) := Subgroup.le_normalizer
  have hIEN : I ⊔ E ≤ Subgroup.normalizer (I : Set G) := sup_le hIN hEN
  have hBN : B ≤ Subgroup.normalizer (I : Set G) := fun x hx => hIEN (hBX hx).1
  have hSN : pushingUpS T ≤ Subgroup.normalizer (I : Set G) := (pushingUpS_le T).trans hTN
  have hSp : pushingUpS T ≤ T := pushingUpS_le T
  have hBp : IsPGroup p B := IsPGroup.of_card hBcard
  have hinjB : ∀ x ∈ B, ∀ hx : x ∈ Subgroup.normalizer (I : Set G),
      U5Act I e ⟨x, hx⟩ = 1 → x = 1 := fun x hxB hxN h => eq_one_of_isPGroup hp hodp hBp hxB hxN h
  have hBhel := isElementaryAbelian_rm (ρ := U5Act I e) (N := Subgroup.normalizer (I : Set G)) hBel
  have hBhcard : Nat.card (rm (Subgroup.normalizer (I : Set G)) (U5Act I e) B) = p ^ 2 := by
    rw [card_rm hBN (injective_comp_subtype hinjB), hBcard]
  have hBhle : rm (Subgroup.normalizer (I : Set G)) (U5Act I e) B ≤
      Subgroup.normalizer (pushingUpS (rm (Subgroup.normalizer (I : Set G)) (U5Act I e) T) :
        Set (MulAut (projSU 5 2 f))) ⊓ U5Inndiag f := by
    refine le_inf ?_ ?_
    · rw [← F.image_S]
      exact rm_le_normalizer (fun x hx => (hBX hx).2)
    · intro a ha
      obtain ⟨b, hbN, hbB, rfl⟩ := mem_rm.1 ha
      exact hEinn b hbN (hBE hbB)
  obtain ⟨bh, hbhB, hbh1, hbhc⟩ := F.model.faithful _ hBhle hBhel hBhcard
  obtain ⟨b, hbN, hbB, hb⟩ := mem_rm.1 hbhB
  have hbnorm : b ∈ Subgroup.normalizer (pushingUpS T : Set G) := (hBX hbB).2
  have hbV : b ∈ Subgroup.centralizer (zOf (pushingUpS T) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    obtain ⟨hvS, hvc⟩ := mem_zOf_iff.1 hv
    have hbn := Subgroup.mem_normalizer_iff.1 hbnorm
    have hbvS : b * v * b⁻¹ ∈ pushingUpS T := (hbn v).1 hvS
    have hbvZ : b * v * b⁻¹ ∈ zOf (pushingUpS T) := by
      refine mem_zOf_iff.2 ⟨hbvS, fun s hs => ?_⟩
      have h1 : b⁻¹ * s * b ∈ pushingUpS T := by
        have := (hbn (b⁻¹ * s * b)).2 (by simpa [mul_assoc] using hs)
        exact this
      have h2 := hvc _ h1
      calc s * (b * v * b⁻¹) = b * ((b⁻¹ * s * b) * v) * b⁻¹ := by group
        _ = b * (v * (b⁻¹ * s * b)) * b⁻¹ := by rw [h2]
        _ = (b * v * b⁻¹) * s := by group
    have hcZ : (b * v * b⁻¹) * v⁻¹ ∈ zOf (pushingUpS T) :=
      (zOf (pushingUpS T)).mul_mem hbvZ ((zOf (pushingUpS T)).inv_mem hv)
    have hcT : (b * v * b⁻¹) * v⁻¹ ∈ T := hSp (zOf_le _ hcZ)
    have hcN : (b * v * b⁻¹) * v⁻¹ ∈ Subgroup.normalizer (I : Set G) := hTN hcT
    have hvN : v ∈ Subgroup.normalizer (I : Set G) := hSN hvS
    have hρv : U5Act I e ⟨v, hvN⟩ ∈ zOf (pushingUpS (rm (Subgroup.normalizer (I : Set G))
        (U5Act I e) T)) := by
      rw [← F.image_Z]
      exact mem_rm.2 ⟨v, hvN, hv, rfl⟩
    have hcomm := Subgroup.mem_centralizer_iff.1 hbhc _ hρv
    rw [← hb] at hcomm
    have hc1 : (b * v * b⁻¹) * v⁻¹ = 1 := by
      refine F.inj _ hcT hcN ?_
      have hbvN : b * v * b⁻¹ ∈ Subgroup.normalizer (I : Set G) :=
        (Subgroup.normalizer (I : Set G)).mul_mem
          ((Subgroup.normalizer (I : Set G)).mul_mem hbN hvN)
          ((Subgroup.normalizer (I : Set G)).inv_mem hbN)
      show U5Act I e (⟨b * v * b⁻¹, hbvN⟩ * ⟨v, hvN⟩⁻¹) = 1
      rw [map_mul, map_inv, show (⟨b * v * b⁻¹, hbvN⟩ : ↥(Subgroup.normalizer (I : Set G))) =
        ⟨b, hbN⟩ * ⟨v, hvN⟩ * ⟨b, hbN⟩⁻¹ from rfl, map_mul, map_mul, map_inv]
      rw [mul_assoc, ← hcomm]
      group
    have : b * v * b⁻¹ = v := by
      have := mul_inv_eq_one.1 hc1
      exact this
    calc v * b = (b * v * b⁻¹) * b := by rw [this]
      _ = b * v := by group
  refine ⟨b, hbB, ?_, hbV, ?_⟩
  · rintro rfl
    apply hbh1
    rw [← hb]
    exact map_one _
  · intro R hRS hRX hRne
    have hRT : R ≤ T := hRS.trans hSp
    have hRN : R ≤ Subgroup.normalizer (I : Set G) := hRT.trans hTN
    have hnorm : U5Inn f ⊓ Subgroup.normalizer
        (pushingUpS (rm (Subgroup.normalizer (I : Set G)) (U5Act I e) T) :
          Set (MulAut (projSU 5 2 f))) ≤
        Subgroup.normalizer (rm (Subgroup.normalizer (I : Set G)) (U5Act I e) R :
          Set (MulAut (projSU 5 2 f))) := by
      intro a ha
      obtain ⟨y, hyN, hyI, hyS, rfl⟩ := F.lift a ha
      exact map_mem_normalizer_rm hyN (hRX ⟨Subgroup.mem_sup_left hyI, hyS⟩)
    have hle : rm (Subgroup.normalizer (I : Set G)) (U5Act I e) R ≤
        pushingUpS (rm (Subgroup.normalizer (I : Set G)) (U5Act I e) T) := by
      rw [← F.image_S]
      exact rm_mono hRS
    rcases F.model.irreducible _ hle hnorm with h | h | h
    · have : R = ⊥ := by
        rw [eq_bot_iff]
        intro r hr
        have hrN := hRN hr
        have h1 : U5Act I e ⟨r, hrN⟩ ∈ rm (Subgroup.normalizer (I : Set G)) (U5Act I e) R :=
          mem_rm.2 ⟨r, hrN, hr, rfl⟩
        rw [h] at h1
        exact (Subgroup.mem_bot.2 (F.inj r (hRT hr) hrN (Subgroup.mem_bot.1 h1)))
      rw [this]
      exact Subgroup.mem_centralizer_iff.2 fun r hr => by
        rw [Subgroup.coe_bot, Set.mem_singleton_iff] at hr
        rw [hr]
        simp
    · have hRV : R ≤ zOf (pushingUpS T) := by
        refine le_of_rm_le_rm (ρ := U5Act I e) hRT ((zOf_le _).trans hSp) hTN F.inj ?_
        rw [F.image_Z, ← h]
      intro r hr
      exact Subgroup.mem_centralizer_iff.1 hbV r (hRV hr)
    · exfalso
      apply hRne
      apply le_antisymm hRS
      refine le_of_rm_le_rm (ρ := U5Act I e) hSp hRT hTN F.inj ?_
      rw [F.image_S, ← h]

theorem core_pure (hM : U5Model) {f p : ℕ} (hf : 1 ≤ f) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpf : p ∣ 2 ^ f + 1) {I E T R : Subgroup G} (e : ↥I ⧸ Subgroup.center ↥I ≃* projSU 5 2 f)
    (hT : IsSylowOf 2 T (Subgroup.normalizer (I : Set G)))
    (hodd : ¬ 2 ∣ Nat.card (U5Act I e).ker) (hR2 : IsPGroup 2 R)
    (hRN : R ≤ Subgroup.normalizer (I : Set G))
    (hRX : (I ⊔ E) ⊓ Subgroup.normalizer (pushingUpS T : Set G) ≤
      Subgroup.normalizer (R : Set G)) :
    R ≤ pushingUpS T := by
  classical
  have F := u5Facts hM hf hp hp5 hpf e hT hodd
  have hTN : T ≤ Subgroup.normalizer (I : Set G) := hT.1
  have hSp : pushingUpS T ≤ T := pushingUpS_le T
  have hnorm : U5Inn f ⊓ Subgroup.normalizer
      (pushingUpS (rm (Subgroup.normalizer (I : Set G)) (U5Act I e) T) :
        Set (MulAut (projSU 5 2 f))) ≤
      Subgroup.normalizer (rm (Subgroup.normalizer (I : Set G)) (U5Act I e) R :
        Set (MulAut (projSU 5 2 f))) := by
    intro a ha
    obtain ⟨y, hyN, hyI, hyS, rfl⟩ := F.lift a ha
    exact map_mem_normalizer_rm hyN (hRX ⟨Subgroup.mem_sup_left hyI, hyS⟩)
  have hRh2 : IsPGroup 2 (rm (Subgroup.normalizer (I : Set G)) (U5Act I e) R) :=
    (hR2.comap_subtype).map _
  have hcore := F.model.core _ hRh2 hnorm
  rw [← F.image_S] at hcore
  have hSR : pushingUpS T ≤ Subgroup.normalizer (R : Set G) := fun s hs =>
    hRX ⟨Subgroup.mem_sup_left (F.S_le hs), Subgroup.le_normalizer hs⟩
  have hS2 : IsPGroup 2 (pushingUpS T) := hT.2.1.to_le hSp
  have hQ2 : IsPGroup 2 ↥(pushingUpS T ⊔ R) := hS2.to_sup_of_normal_right' hR2 hSR
  intro r hr
  have hrN := hRN hr
  obtain ⟨s, hsN, hsS, hs⟩ := mem_rm.1 (hcore (mem_rm.2 ⟨r, hrN, hr, rfl⟩))
  have hcQ : s⁻¹ * r ∈ pushingUpS T ⊔ R :=
    mul_mem (inv_mem (Subgroup.mem_sup_left hsS)) (Subgroup.mem_sup_right hr)
  have hc1 : s⁻¹ * r = 1 := eq_one_of_isPGroup_two (ρ := U5Act I e) hodd hQ2 hcQ
    ((Subgroup.normalizer (I : Set G)).mul_mem ((Subgroup.normalizer (I : Set G)).inv_mem hsN) hrN)
    (by
      show U5Act I e (⟨s, hsN⟩⁻¹ * ⟨r, hrN⟩) = 1
      rw [map_mul, map_inv, hs, inv_mul_cancel])
  have : r = s := (inv_mul_eq_one.1 hc1).symm
  rw [this]
  exact hsS

theorem syl_pure (hM : U5Model) {f p : ℕ} (hf : 1 ≤ f) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpf : p ∣ 2 ^ f + 1) {I T P : Subgroup G} (e : ↥I ⧸ Subgroup.center ↥I ≃* projSU 5 2 f)
    (hT : IsSylowOf 2 T (Subgroup.normalizer (I : Set G)))
    (hodd : ¬ 2 ∣ Nat.card (U5Act I e).ker) (hodp : ¬ p ∣ Nat.card (U5Act I e).ker)
    (hPN : P ≤ Subgroup.normalizer (I : Set G)) (hPp : IsPGroup p P)
    (hPC : P ≤ Subgroup.centralizer (zOf (pushingUpS T) : Set G)) : IsCyclic ↥P := by
  classical
  have F := u5Facts hM hf hp hp5 hpf e hT hodd
  have hinjP : Function.Injective ((U5Act I e).comp
      (P.subgroupOf (Subgroup.normalizer (I : Set G))).subtype) :=
    injective_comp_subtype fun x hxP hxN h => eq_one_of_isPGroup hp hodp hPp hxP hxN h
  have hPhp : IsPGroup p (rm (Subgroup.normalizer (I : Set G)) (U5Act I e) P) :=
    (hPp.comap_subtype).map _
  have hPhc : rm (Subgroup.normalizer (I : Set G)) (U5Act I e) P ≤
      Subgroup.centralizer (zOf (pushingUpS (rm (Subgroup.normalizer (I : Set G)) (U5Act I e) T)) :
        Set (MulAut (projSU 5 2 f))) := by
    intro a ha
    obtain ⟨x, hxN, hxP, rfl⟩ := mem_rm.1 ha
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [← F.image_Z] at hz
    obtain ⟨v, hvN, hvZ, rfl⟩ := mem_rm.1 hz
    have hvx := Subgroup.mem_centralizer_iff.1 (hPC hxP) v hvZ
    rw [← map_mul, ← map_mul]
    exact congrArg _ (Subtype.ext hvx)
  have hcyc := F.model.cyclic _ hPhp hPhc
  let eq : ↥P ≃* ↥(rm (Subgroup.normalizer (I : Set G)) (U5Act I e) P) :=
    (Subgroup.subgroupOfEquivOfLe hPN).symm.trans (equivMapOfInjOn _ hinjP)
  exact isCyclic_of_surjective eq.symm.toMonoidHom eq.symm.surjective

end CFSG.RankThree.PartOne.U5K
