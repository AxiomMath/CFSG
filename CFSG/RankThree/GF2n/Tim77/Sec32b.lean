module

public import CFSG.RankThree.GF2n.Tim77.Sec3Basic
import all CFSG.Timmesfeld.RootInvolutions.RootInvolutionSetting
public import CFSG.Quasithin.Background.F1Models

public section

namespace CFSG.RankThree.GF2n.Tim77

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Timmesfeld.RootInvolutions Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G]

theorem sec32b_mem_normalizer_conj {k x : G} {T : Subgroup G} :
    x ∈ normalizer (conjSubgroup k T : Set G) ↔ k⁻¹ * x * k ∈ normalizer (T : Set G) := by
  rw [Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
  constructor
  · intro hx w
    have h1 := hx (k * w * k⁻¹)
    rw [mem_conjSubgroup, mem_conjSubgroup] at h1
    have e1 : k⁻¹ * (k * w * k⁻¹) * k = w := by group
    have e2 : k⁻¹ * (x * (k * w * k⁻¹) * x⁻¹) * k = (k⁻¹ * x * k) * w * (k⁻¹ * x * k)⁻¹ := by
      group
    rw [e1, e2] at h1
    exact h1
  · intro hx z
    have h1 := hx (k⁻¹ * z * k)
    rw [mem_conjSubgroup, mem_conjSubgroup]
    have e2 : (k⁻¹ * x * k) * (k⁻¹ * z * k) * (k⁻¹ * x * k)⁻¹ = k⁻¹ * (x * z * x⁻¹) * k := by
      group
    rw [e2] at h1
    exact h1

theorem sec32b_exists_ne_one {H : Subgroup G} (h : H ≠ ⊥) : ∃ a ∈ H, a ≠ 1 := by
  obtain ⟨⟨a, ha⟩, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp h
  exact ⟨a, ha, fun h1 => ha1 (Subtype.ext h1)⟩

theorem sec32b_isPGroup {E : Subgroup G} (hE : IsElemAbelian 2 E) : IsPGroup 2 E := by
  intro x
  refine ⟨1, Subtype.ext ?_⟩
  simpa using hE.2 x x.2

theorem sec32b_mem_smul_sylow {P : Sylow 2 G} {k z : G} :
    z ∈ ((k • P : Sylow 2 G) : Subgroup G) ↔ k⁻¹ * z * k ∈ (P : Subgroup G) := by
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv,
    MulAut.smul_def, MulAut.conj_apply, inv_inv]

theorem sec32b_exists_fixed [Finite G] {K H : Subgroup G} (hK : IsPGroup 2 K)
    (hH : IsPGroup 2 H) (hKH : K ≤ normalizer (H : Set G)) (hne : H ≠ ⊥) :
    ∃ t ∈ H, t ≠ 1 ∧ ∀ k ∈ K, k * t = t * k := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set L := K ⊔ H with hL
  have hLp : IsPGroup 2 L := hK.to_sup_of_normal_right' hH hKH
  have hHL : H ≤ L := le_sup_right
  have hnormL : ∀ x ∈ L, x ∈ normalizer (H : Set G) :=
    fun x hx => (sup_le hKH Subgroup.le_normalizer) hx
  have hnorm : (H.subgroupOf L).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hHL]
    intro h k hh hk
    exact (Subgroup.mem_normalizer_iff.1 (hnormL k hk) h).1 hh
  have hnil : Group.IsNilpotent L := hLp.isNilpotent
  have hne' : H.subgroupOf L ≠ ⊥ := by
    intro h
    apply hne
    rw [eq_bot_iff]
    intro x hx
    have : (⟨x, hHL hx⟩ : L) ∈ H.subgroupOf L := hx
    rw [h, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.2 (congrArg Subtype.val this)
  obtain ⟨⟨z, hz⟩, hz1⟩ :=
    (Subgroup.ne_bot_iff_exists_ne_one.1 (Group.IsNilpotent.inf_center_ne_bot_of_normal hne'))
  refine ⟨z.1, hz.1, fun h => hz1 (Subtype.ext (Subtype.ext h)), fun k hk => ?_⟩
  have hc := Subgroup.mem_center_iff.1 hz.2 ⟨k, (le_sup_left : K ≤ L) hk⟩
  exact congrArg Subtype.val hc

theorem sec32b_commute_of_normalizes [Finite G] {A : Subgroup G} (hA : IsElemAbelian 2 A)
    (hTI : IsTI A) (g h : G)
    (hgh : conjSubgroup g A ≤ normalizer (conjSubgroup h A : Set G)) :
    ∀ x ∈ conjSubgroup g A, ∀ y ∈ conjSubgroup h A, x * y = y * x := by
  have hCel : IsElemAbelian 2 (conjSubgroup h A) := isElemAbelian_conj hA h
  have hCTI : IsTI (conjSubgroup h A) := isTI_conjSubgroup hTI h
  have hBC : conjSubgroup g A = conjSubgroup (g * h⁻¹) (conjSubgroup h A) := by
    rw [← conjSubgroup_mul, inv_mul_cancel_right]
  have hle : conjSubgroup (g * h⁻¹) (conjSubgroup h A) ≤
      normalizer (conjSubgroup h A : Set G) := by
    rw [← hBC]; exact hgh
  have hel := tim77_2_3 hCel hCTI hle
  intro x hx y hy
  have hx' : x ∈ conjSubgroup h A ⊔ conjSubgroup (g * h⁻¹) (conjSubgroup h A) :=
    Subgroup.mem_sup_right (hBC ▸ hx)
  have hy' : y ∈ conjSubgroup h A ⊔ conjSubgroup (g * h⁻¹) (conjSubgroup h A) :=
    Subgroup.mem_sup_left hy
  exact congrArg Subtype.val (hel.1.is_comm.comm ⟨x, hx'⟩ ⟨y, hy'⟩)

theorem sec32b_root_contra {A Ab : Subgroup G} {g t : G}
    (hroot : ∀ k : G, conjSubgroup k A ≤ centralizer (A : Set G) →
      IsRootTypeIn 2 (centralizer (A : Set G)) (conjSubgroup k A))
    (hAb : Ab = conjSubgroup t A) (ht : t ∈ A ⊔ Ab)
    (hX : ∀ x ∈ A ⊔ Ab, ∀ y ∈ conjSubgroup g A, x * y = y * x)
    (hN : normalizerIn A Ab ≠ ⊥) :
    ∀ a ∈ A, ∀ b ∈ Ab, a * b = b * a := by
  have hmem1 : ∀ w : G, w ∈ conjSubgroup g⁻¹ A ↔ g * w * g⁻¹ ∈ A := fun w => by
    rw [mem_conjSubgroup, inv_inv]
  have hmem2 : ∀ a ∈ A, g * a * g⁻¹ ∈ conjSubgroup g A := fun a ha => by
    rw [mem_conjSubgroup]
    have e : g⁻¹ * (g * a * g⁻¹) * g = a := by group
    rw [e]; exact ha
  have hle : conjSubgroup g⁻¹ A ≤ centralizer (A : Set G) := by
    intro w hw
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    have h1 := hX _ (Subgroup.mem_sup_left ((hmem1 w).mp hw)) _ (hmem2 a ha)
    calc a * w = g⁻¹ * ((g * a * g⁻¹) * (g * w * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * w * g⁻¹) * (g * a * g⁻¹)) * g := by rw [h1]
      _ = w * a := by group
  obtain ⟨_, _, _, hroot4⟩ := hroot g⁻¹ hle
  have hh' : g⁻¹ * t * g ∈ centralizer (A : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    have h1 := hX t ht _ (hmem2 a ha)
    calc a * (g⁻¹ * t * g) = g⁻¹ * ((g * a * g⁻¹) * t) * g := by group
      _ = g⁻¹ * (t * (g * a * g⁻¹)) * g := by rw [h1]
      _ = (g⁻¹ * t * g) * a := by group
  have hconj : conjSubgroup (g⁻¹ * t * g) (conjSubgroup g⁻¹ A) = conjSubgroup g⁻¹ Ab := by
    rw [← conjSubgroup_mul, hAb, ← conjSubgroup_mul]
    congr 1
    group
  obtain ⟨a₀, ha₀, ha₀1⟩ := sec32b_exists_ne_one hN
  have ha₀' : a₀ ∈ A ⊓ normalizer (Ab : Set G) := by
    unfold normalizerIn at ha₀; exact ha₀
  have hne : normalizerIn (conjSubgroup g⁻¹ A)
      (conjSubgroup (g⁻¹ * t * g) (conjSubgroup g⁻¹ A)) ≠ ⊥ := by
    rw [hconj]
    intro hbot
    have hmemN : g⁻¹ * a₀ * g ∈ normalizerIn (conjSubgroup g⁻¹ A) (conjSubgroup g⁻¹ Ab) := by
      unfold normalizerIn
      have e : (g⁻¹)⁻¹ * (g⁻¹ * a₀ * g) * g⁻¹ = a₀ := by group
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · rw [mem_conjSubgroup, e]; exact (Subgroup.mem_inf.mp ha₀').1
      · rw [sec32b_mem_normalizer_conj, e]; exact (Subgroup.mem_inf.mp ha₀').2
    rw [hbot, Subgroup.mem_bot] at hmemN
    apply ha₀1
    have e : a₀ = g * (g⁻¹ * a₀ * g) * g⁻¹ := by group
    rw [e, hmemN]; group
  have key := hroot4 _ hh' hne
  intro a ha b hb
  have ha' : g⁻¹ * a * g ∈ conjSubgroup g⁻¹ A := by
    rw [mem_conjSubgroup]
    have e : (g⁻¹)⁻¹ * (g⁻¹ * a * g) * g⁻¹ = a := by group
    rw [e]; exact ha
  have hb' : g⁻¹ * b * g ∈ conjSubgroup (g⁻¹ * t * g) (conjSubgroup g⁻¹ A) := by
    rw [hconj, mem_conjSubgroup]
    have e : (g⁻¹)⁻¹ * (g⁻¹ * b * g) * g⁻¹ = b := by group
    rw [e]; exact hb
  have h1 := key _ ha' _ hb'
  calc a * b = g * ((g⁻¹ * a * g) * (g⁻¹ * b * g)) * g⁻¹ := by group
    _ = g * ((g⁻¹ * b * g) * (g⁻¹ * a * g)) * g⁻¹ := by rw [h1]
    _ = b * a := by group

theorem sec32b_mem_conj {A : Subgroup G} {b : G} (n : G) (hb : b ∈ A) :
    n * b * n⁻¹ ∈ conjSubgroup n A := by
  rw [mem_conjSubgroup]
  have e : n⁻¹ * (n * b * n⁻¹) * n = b := by group
  rw [e]; exact hb

theorem sec32b_mul_conj_mem_centralizer {A : Subgroup G} (hA : IsElemAbelian 2 A) {n b : G}
    (hb : b ∈ A) (hcomm : ∀ a ∈ A, ∀ e ∈ conjSubgroup n A, a * e = e * a) :
    b * (n * b * n⁻¹) ∈ centralizer (A : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro a ha
  have h1 : a * b = b * a := congrArg Subtype.val (hA.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have h2 : a * (n * b * n⁻¹) = (n * b * n⁻¹) * a := hcomm a ha _ (sec32b_mem_conj n hb)
  calc a * (b * (n * b * n⁻¹)) = (a * b) * (n * b * n⁻¹) := by group
    _ = (b * a) * (n * b * n⁻¹) := by rw [h1]
    _ = b * (a * (n * b * n⁻¹)) := by group
    _ = b * ((n * b * n⁻¹) * a) := by rw [h2]
    _ = (b * (n * b * n⁻¹)) * a := by group

theorem sec32b_commutator_mem_centralizer {A : Subgroup G} {u x : G}
    (hu : u ∈ centralizer (A : Set G)) (hx : x ∈ normalizer (A : Set G)) :
    u * x * u⁻¹ * x⁻¹ ∈ centralizer (A : Set G) := by
  have hxu : x * u⁻¹ * x⁻¹ ∈ centralizer (A : Set G) :=
    (Subgroup.mem_normalizer_iff.mp (mem_normalizer_centralizer hx) _).mp
      ((centralizer (A : Set G)).inv_mem hu)
  have e : u * x * u⁻¹ * x⁻¹ = u * (x * u⁻¹ * x⁻¹) := by group
  rw [e]
  exact (centralizer (A : Set G)).mul_mem hu hxu

theorem sec32b_mem_centralizer_of_commute [Finite G] {A : Subgroup G} (hTI : IsTI A) {n x a₁ : G}
    (hAn : conjSubgroup n A ≠ A) (hxN : x ∈ normalizer (A : Set G)) (ha₁ : a₁ ∈ A)
    (ha₁1 : a₁ ≠ 1) (hxa₁ : a₁ * x = x * a₁)
    (hall : ∀ b ∈ A, (b * (n * b * n⁻¹)) * x = x * (b * (n * b * n⁻¹))) :
    x ∈ centralizer (A : Set G) := by
  have hxe : x * (n * a₁ * n⁻¹) = (n * a₁ * n⁻¹) * x := by
    have h1 := hall a₁ ha₁
    have h3 : a₁ * ((n * a₁ * n⁻¹) * x) = a₁ * (x * (n * a₁ * n⁻¹)) := by
      calc a₁ * ((n * a₁ * n⁻¹) * x) = (a₁ * (n * a₁ * n⁻¹)) * x := by group
        _ = x * (a₁ * (n * a₁ * n⁻¹)) := h1
        _ = (x * a₁) * (n * a₁ * n⁻¹) := by group
        _ = (a₁ * x) * (n * a₁ * n⁻¹) := by rw [hxa₁]
        _ = a₁ * (x * (n * a₁ * n⁻¹)) := by group
    exact (mul_left_cancel h3).symm
  have hxn : x ∈ normalizer (conjSubgroup n A : Set G) :=
    mem_normalizer_of_commute_of_isTI (isTI_conjSubgroup hTI n) (sec32b_mem_conj n ha₁)
      (fun h1 => ha₁1 (conj_eq_one_iff.mp h1)) hxe
  have hbot : A ⊓ conjSubgroup n A = ⊥ := inf_conjSubgroup_eq_bot_of_isTI hTI hAn
  rw [Subgroup.mem_centralizer_iff]
  intro b hb
  have hbn := sec32b_mem_conj n hb
  have hb' : x * b * x⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp hxN b).mp hb
  have hbn' : x * (n * b * n⁻¹) * x⁻¹ ∈ conjSubgroup n A :=
    (Subgroup.mem_normalizer_iff.mp hxn _).mp hbn
  have h1 := hall b hb
  have hprod : (x * b * x⁻¹) * (x * (n * b * n⁻¹) * x⁻¹) = b * (n * b * n⁻¹) := by
    calc (x * b * x⁻¹) * (x * (n * b * n⁻¹) * x⁻¹)
        = (x * (b * (n * b * n⁻¹))) * x⁻¹ := by group
      _ = ((b * (n * b * n⁻¹)) * x) * x⁻¹ := by rw [h1]
      _ = b * (n * b * n⁻¹) := by group
  have h2 := eq_mul_inv_of_mul_eq hprod
  have heq : b⁻¹ * (x * b * x⁻¹) = (n * b * n⁻¹) * (x * (n * b * n⁻¹) * x⁻¹)⁻¹ := by
    rw [h2]; group
  have hmem : b⁻¹ * (x * b * x⁻¹) ∈ A ⊓ conjSubgroup n A :=
    Subgroup.mem_inf.mpr ⟨A.mul_mem (A.inv_mem hb) hb', by
      rw [heq]; exact (conjSubgroup n A).mul_mem hbn ((conjSubgroup n A).inv_mem hbn')⟩
  rw [hbot, Subgroup.mem_bot] at hmem
  have h3 : x * b * x⁻¹ = b := by
    calc x * b * x⁻¹ = b * (b⁻¹ * (x * b * x⁻¹)) := by group
      _ = b := by rw [hmem, mul_one]
  calc b * x = (x * b * x⁻¹) * x := by rw [h3]
    _ = x * b := by group

theorem sec32b_core [Finite G] {A Ab L Lb M Y N N₀ : Subgroup G}
    (S : Prop24Setup A Ab L Lb M)
    (hroot : ∀ k : G, conjSubgroup k A ≤ centralizer (A : Set G) →
      IsRootTypeIn 2 (centralizer (A : Set G)) (conjSubgroup k A))
    (hsyl : ∃ P : Sylow 2 G, (P : Subgroup G) ≤ normalizer (A : Set G))
    (hAY : A ≤ Y) (hAbY : Ab ≤ Y) (hLN : L ≤ N)
    (hYN : ∀ y ∈ Y, y ∈ normalizer (N : Set G)) (hNel : IsElemAbelian 2 N)
    (hN₀Y : N₀ ≤ Y) (hN₀p : IsPGroup 2 N₀) (hYN₀ : Y ≤ normalizer (N₀ : Set G))
    (hLN₀ : L ≤ N₀) : N₀ ≤ normalizer (A : Set G) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hN₀n : ∀ y ∈ Y, ∀ n ∈ N₀, y * n * y⁻¹ ∈ N₀ := fun y hy n hn =>
    (Subgroup.mem_normalizer_iff.mp (hYN₀ hy) n).mp hn
  intro n hn
  by_contra hnN
  have hnY : n ∈ Y := hN₀Y hn
  have hAn : conjSubgroup n A ≠ A := fun hc => hnN (conjSubgroup_eq_self_iff.mp hc)
  obtain ⟨a₁, ha₁L, ha₁1⟩ := sec32b_exists_ne_one S.ne_bot
  have ha₁A : a₁ ∈ A := S.L_le ha₁L
  have hLn : L ≤ normalizer (conjSubgroup n A : Set G) := by
    intro a₀ ha₀
    have he₁N : n * a₁ * n⁻¹ ∈ N :=
      (Subgroup.mem_normalizer_iff.mp (hYN n hnY) a₁).mp (hLN ha₁L)
    have hcomm : a₀ * (n * a₁ * n⁻¹) = (n * a₁ * n⁻¹) * a₀ :=
      congrArg Subtype.val (hNel.1.is_comm.comm ⟨a₀, hLN ha₀⟩ ⟨_, he₁N⟩)
    exact mem_normalizer_of_commute_of_isTI (isTI_conjSubgroup S.ti n) (sec32b_mem_conj n ha₁A)
      (fun h1 => ha₁1 (conj_eq_one_iff.mp h1)) hcomm
  have hP₀ : IsPGroup 2 ↥(A ⊔ N₀) :=
    (sec32b_isPGroup S.elem).to_sup_of_normal_right' hN₀p (hAY.trans hYN₀)
  have hAnle : conjSubgroup n A ≤ A ⊔ N₀ := by
    intro z hz
    rw [mem_conjSubgroup] at hz
    have h1 : (n⁻¹ * z * n) * n⁻¹ * (n⁻¹ * z * n)⁻¹ ∈ N₀ :=
      hN₀n _ (hAY hz) n⁻¹ (N₀.inv_mem hn)
    have h2 : n * ((n⁻¹ * z * n) * n⁻¹ * (n⁻¹ * z * n)⁻¹) ∈ N₀ := N₀.mul_mem hn h1
    have e : z = (n * ((n⁻¹ * z * n) * n⁻¹ * (n⁻¹ * z * n)⁻¹)) * (n⁻¹ * z * n) := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right h2) (Subgroup.mem_sup_left hz)
  have hnb : normalizerIn A (conjSubgroup n A) ≠ ⊥ := by
    intro hbot
    have hmem : a₁ ∈ normalizerIn A (conjSubgroup n A) := by
      unfold normalizerIn
      exact Subgroup.mem_inf.mpr ⟨ha₁A, hLn ha₁L⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    exact ha₁1 hmem
  have hcomm : ∀ a ∈ A, ∀ e ∈ conjSubgroup n A, a * e = e * a := by
    have := commute_of_isPGroup S.elem S.ti (g := 1) (h := n)
      (by rw [conjSubgroup_one]; exact hP₀.to_le (sup_le le_sup_left hAnle))
      (by rw [conjSubgroup_one]; exact hnb)
    rw [conjSubgroup_one] at this
    exact this
  obtain ⟨P₁, hP₁⟩ := hsyl
  have hQp : IsPGroup 2 ↥(Ab ⊔ N₀) :=
    (sec32b_isPGroup S.elem_Ab).to_sup_of_normal_right' hN₀p (hAbY.trans hYN₀)
  obtain ⟨P, hQP⟩ := hQp.exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq G P₁ P
  have hPN : (P : Subgroup G) ≤ normalizer (conjSubgroup c A : Set G) := by
    intro z hz
    rw [sec32b_mem_normalizer_conj]
    rw [← hc] at hz
    exact hP₁ (sec32b_mem_smul_sylow.mp hz)
  have hAbP : Ab ≤ (P : Subgroup G) := le_sup_left.trans hQP
  have hN₀P : N₀ ≤ (P : Subgroup G) := le_sup_right.trans hQP
  have hA'el : IsElemAbelian 2 (conjSubgroup c A) := isElemAbelian_conj S.elem c
  have hA'P : conjSubgroup c A ≤ (P : Subgroup G) := by
    have hsup : IsPGroup 2 ↥((P : Subgroup G) ⊔ conjSubgroup c A) :=
      P.isPGroup'.to_sup_of_normal_right' (sec32b_isPGroup hA'el) hPN
    exact le_sup_right.trans (P.is_maximal' hsup le_sup_left).le
  obtain ⟨g₀, hg₀⟩ := S.conj
  have hAbA' : ∀ b ∈ Ab, ∀ z ∈ conjSubgroup c A, b * z = z * b := by
    have hP2 : IsPGroup 2 ↥(conjSubgroup g₀ A ⊔ conjSubgroup c A) := by
      rw [← hg₀]
      exact P.isPGroup'.to_le (sup_le hAbP hA'P)
    have hnb' : normalizerIn (conjSubgroup g₀ A) (conjSubgroup c A) ≠ ⊥ := by
      rw [← hg₀]
      intro hbot
      have hle : Ab ≤ normalizer (conjSubgroup c A : Set G) := hAbP.trans hPN
      have : normalizerIn Ab (conjSubgroup c A) = Ab := by
        unfold normalizerIn; exact inf_eq_left.mpr hle
      rw [this] at hbot
      exact S.Ab_ne_bot hbot
    have := commute_of_isPGroup S.elem S.ti hP2 hnb'
    rwa [← hg₀] at this
  have hA'ne : conjSubgroup c A ≠ ⊥ := by
    intro hbot
    apply S.A_ne_bot
    have h1 := card_conjSubgroup c A
    rw [hbot, Subgroup.card_bot] at h1
    exact Subgroup.card_eq_one.mp h1.symm
  obtain ⟨x, hxA', hx1, hxfix⟩ := sec32b_exists_fixed (K := L) (H := conjSubgroup c A)
    ((sec32b_isPGroup S.elem).to_le S.L_le) (sec32b_isPGroup hA'el)
    (hLN₀.trans (hN₀P.trans hPN)) hA'ne
  have hxN : x ∈ normalizer (A : Set G) :=
    mem_normalizer_of_commute_of_isTI S.ti ha₁A ha₁1 (hxfix a₁ ha₁L).symm
  have key : ∃ y ∈ conjSubgroup c A, y ≠ 1 ∧ y ∈ centralizer (A : Set G) := by
    by_cases hall : ∀ b ∈ A, (b * (n * b * n⁻¹)) * x = x * (b * (n * b * n⁻¹))
    · exact ⟨x, hxA', hx1,
        sec32b_mem_centralizer_of_commute S.ti hAn hxN ha₁A ha₁1 (hxfix a₁ ha₁L) hall⟩
    · push Not at hall
      obtain ⟨b, hb, hbx⟩ := hall
      have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_right (S.sq_A hb)
      have huN : b * (n * b * n⁻¹) ∈ N₀ := by
        have e : b * (n * b * n⁻¹) = (b * n * b⁻¹) * n⁻¹ := by rw [hbinv]; group
        rw [e]
        exact N₀.mul_mem (hN₀n b (hAY hb) n hn) (N₀.inv_mem hn)
      have huC := sec32b_mul_conj_mem_centralizer S.elem hb hcomm
      have huP : b * (n * b * n⁻¹) ∈ normalizer (conjSubgroup c A : Set G) :=
        hPN (hN₀P huN)
      generalize b * (n * b * n⁻¹) = u at huC huP hbx
      refine ⟨u * x * u⁻¹ * x⁻¹, (conjSubgroup c A).mul_mem
        ((Subgroup.mem_normalizer_iff.mp huP x).mp hxA') ((conjSubgroup c A).inv_mem hxA'),
        fun h1 => hbx ?_, sec32b_commutator_mem_centralizer huC hxN⟩
      calc u * x = u * x * u⁻¹ * x⁻¹ * (x * u) := by group
        _ = x * u := by rw [h1, one_mul]
  obtain ⟨y, hyA', hy1, hyC⟩ := key
  have hAN' : A ≤ normalizer (conjSubgroup c A : Set G) := fun a ha =>
    mem_normalizer_of_commute_of_isTI (isTI_conjSubgroup S.ti c) hyA' hy1
      (Subgroup.mem_centralizer_iff.mp hyC a ha)
  have hAA' : ∀ a ∈ A, ∀ z ∈ conjSubgroup c A, a * z = z * a := by
    have := sec32b_commute_of_normalizes S.elem S.ti 1 c (by rw [conjSubgroup_one]; exact hAN')
    rw [conjSubgroup_one] at this
    exact this
  have hX : ∀ w ∈ A ⊔ Ab, ∀ z ∈ conjSubgroup c A, w * z = z * w := by
    have hle : A ⊔ Ab ≤ centralizer (conjSubgroup c A : Set G) :=
      sup_le (fun a ha => Subgroup.mem_centralizer_iff.mpr fun z hz => (hAA' a ha z hz).symm)
        (fun b hb => Subgroup.mem_centralizer_iff.mpr fun z hz => (hAbA' b hb z hz).symm)
    intro w hw z hz
    exact (Subgroup.mem_centralizer_iff.mp (hle hw) z hz).symm
  obtain ⟨t, ht, hbt⟩ := S.exists_conj_eq
  have hN' : normalizerIn A Ab ≠ ⊥ := by
    unfold normalizerIn; rw [← S.hL]; exact S.ne_bot
  have hcomm2 := sec32b_root_contra hroot hbt ht hX hN'
  have hle : Ab ≤ normalizer (A : Set G) :=
    le_normalizer_of_comm fun b hb a ha => (hcomm2 a ha b hb).symm
  exact S.Lb_ne (by rw [S.hLb]; exact inf_eq_left.mpr hle)

theorem sec32b_le_normalizer [Finite G] {A Ab L Lb M Y N : Subgroup G}
    (S : Prop24Setup A Ab L Lb M)
    (hroot : ∀ k : G, conjSubgroup k A ≤ centralizer (A : Set G) →
      IsRootTypeIn 2 (centralizer (A : Set G)) (conjSubgroup k A))
    (hsyl : ∃ P : Sylow 2 G, (P : Subgroup G) ≤ normalizer (A : Set G))
    (hAY : A ≤ Y) (hAbY : Ab ≤ Y) (hNY : N ≤ Y) (hLN : L ≤ N)
    (hYN : ∀ y ∈ Y, y ∈ normalizer (N : Set G)) (hNel : IsElemAbelian 2 N) :
    (pCore 2 ↥Y).map Y.subtype ≤ normalizer (A : Set G) := by
  have hNN₀ : N ≤ (pCore 2 ↥Y).map Y.subtype := by
    haveI : (N.subgroupOf Y).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hNY).mpr fun y hy => hYN y hy
    have hp : IsPGroup 2 (N.subgroupOf Y) :=
      (sec32b_isPGroup hNel).comap_of_injective Y.subtype Subtype.val_injective
    have h1 : N.subgroupOf Y ≤ pCore 2 ↥Y := le_sSup ⟨inferInstance, hp⟩
    calc N = (N.subgroupOf Y).map Y.subtype := (Subgroup.map_subgroupOf_eq_of_le hNY).symm
      _ ≤ _ := Subgroup.map_mono h1
  exact sec32b_core S hroot hsyl hAY hAbY hLN hYN hNel (Subgroup.map_subtype_le _)
    ((CFSG.pCore_isPGroup (p := 2) (G := ↥Y)).map Y.subtype)
    (le_normalizer_map_subtype Y (pCore 2 ↥Y)) (hLN.trans hNN₀)

theorem sec32b_commutator_le [Finite G] {A Ab L Lb M Y N N₀ : Subgroup G} {s : G}
    (S : Prop24Setup A Ab L Lb M) (hs : s ∈ centralizer (A : Set G))
    (hY : Y = A ⊔ Ab ⊔ conjSubgroup s Ab) (hN : N = L ⊔ Lb ⊔ conjSubgroup s Lb)
    (hYN : ∀ y ∈ Y, y ∈ normalizer (N : Set G))
    (hN₀n : ∀ y ∈ Y, ∀ n ∈ N₀, y * n * y⁻¹ ∈ N₀)
    (hN₀A : N₀ ≤ normalizer (A : Set G)) : ⁅N₀, Y⁆ ≤ N := by
  have hAY : A ≤ Y := by rw [hY]; exact le_sup_left.trans le_sup_left
  have hAbY : Ab ≤ Y := by rw [hY]; exact le_sup_right.trans le_sup_left
  have hsAbY : conjSubgroup s Ab ≤ Y := by rw [hY]; exact le_sup_right
  have hLN : L ≤ N := by rw [hN]; exact le_sup_left.trans le_sup_left
  have hLbN : Lb ≤ N := by rw [hN]; exact le_sup_right.trans le_sup_left
  have hconjN : ∀ y ∈ Y, N₀ ≤ normalizer (conjSubgroup y A : Set G) := by
    intro y hy n hn
    rw [sec32b_mem_normalizer_conj]
    apply hN₀A
    have := hN₀n y⁻¹ (Y.inv_mem hy) n hn
    simpa using this
  have hsN : s ∈ normalizer (A : Set G) :=
    le_normalizer_of_comm (X := centralizer (A : Set G)) (N := A)
      (fun x hx y hy => (Subgroup.mem_centralizer_iff.mp hx y hy).symm) hs
  have hsA : ∀ a ∈ A, s⁻¹ * a * s = a := fun a ha => by
    have h1 := Subgroup.mem_centralizer_iff.mp hs a ha
    calc s⁻¹ * a * s = s⁻¹ * (a * s) := by group
      _ = s⁻¹ * (s * a) := by rw [h1]
      _ = a := by group
  obtain ⟨t, ht, hbt⟩ := S.exists_conj_eq
  have htY : t ∈ Y := by
    rw [hY]; exact (le_sup_left : A ⊔ Ab ≤ A ⊔ Ab ⊔ conjSubgroup s Ab) ht
  have hAbn : N₀ ≤ normalizer (Ab : Set G) := hbt ▸ hconjN t htY
  have S' : Prop24Setup A (conjSubgroup s Ab) (normalizerIn A (conjSubgroup s Ab))
      (normalizerIn (conjSubgroup s Ab) A)
      (normalizerIn A (conjSubgroup s Ab) ⊔ normalizerIn (conjSubgroup s Ab) A) :=
    { elem := S.elem
      ti := S.ti
      conj := by
        obtain ⟨g, hg⟩ := S.conj
        exact ⟨s * g, by rw [hg, conjSubgroup_mul]⟩
      hL := by unfold normalizerIn; rfl
      hLb := by unfold normalizerIn; rfl
      hM := rfl
      ne_bot := by
        obtain ⟨a₀, ha₀L, ha₀1⟩ := sec32b_exists_ne_one S.ne_bot
        intro hbot
        have hmem : a₀ ∈ normalizerIn A (conjSubgroup s Ab) := by
          unfold normalizerIn
          refine Subgroup.mem_inf.mpr ⟨S.L_le ha₀L, ?_⟩
          rw [sec32b_mem_normalizer_conj, hsA a₀ (S.L_le ha₀L)]
          exact (S.mem_L.mp ha₀L).2
        rw [hbot, Subgroup.mem_bot] at hmem
        exact ha₀1 hmem
      ne := by
        intro h
        apply S.ne
        refine le_antisymm S.L_le fun a ha => S.mem_L.mpr ⟨ha, ?_⟩
        have hmem : a ∈ normalizerIn A (conjSubgroup s Ab) := by rw [h]; exact ha
        unfold normalizerIn at hmem
        have h2 := (Subgroup.mem_inf.mp hmem).2
        rw [sec32b_mem_normalizer_conj, hsA a ha] at h2
        exact h2 }
  obtain ⟨y', hy'Y, hy'⟩ := S'.exists_conj_eq
  have hAsY : A ⊔ conjSubgroup s Ab ≤ Y := by
    rw [hY]; exact sup_le (le_sup_left.trans le_sup_left) le_sup_right
  have hsAbn : N₀ ≤ normalizer (conjSubgroup s Ab : Set G) := hy' ▸ hconjN y' (hAsY hy'Y)
  have hcomm : ∀ T : Subgroup G, T ≤ Y → N₀ ≤ normalizer (T : Set G) →
      ∀ n ∈ N₀, ∀ z ∈ T, ⁅n, z⁆ ∈ T ∧ ⁅n, z⁆ ∈ N₀ := by
    intro T hTY hT n hn z hz
    refine ⟨?_, ?_⟩
    · have h1 : n * z * n⁻¹ ∈ T := (Subgroup.mem_normalizer_iff.mp (hT hn) z).mp hz
      rw [commutatorElement_def]
      exact T.mul_mem h1 (T.inv_mem hz)
    · have h1 : z * n⁻¹ * z⁻¹ ∈ N₀ := hN₀n z (hTY hz) n⁻¹ (N₀.inv_mem hn)
      have e : ⁅n, z⁆ = n * (z * n⁻¹ * z⁻¹) := by
        simp only [commutatorElement_def]; group
      rw [e]
      exact N₀.mul_mem hn h1
  rw [Subgroup.commutator_le]
  let K : Subgroup G :=
    { carrier := {y | y ∈ Y ∧ ∀ n ∈ N₀, ⁅n, y⁆ ∈ N}
      mul_mem' := by
        rintro y₁ y₂ ⟨hy₁Y, hy₁⟩ ⟨hy₂Y, hy₂⟩
        refine ⟨Y.mul_mem hy₁Y hy₂Y, fun n hn => ?_⟩
        have e : ⁅n, y₁ * y₂⁆ = ⁅n, y₁⁆ * (y₁ * ⁅n, y₂⁆ * y₁⁻¹) := by
          simp only [commutatorElement_def]; group
        rw [e]
        exact N.mul_mem (hy₁ n hn)
          ((Subgroup.mem_normalizer_iff.mp (hYN y₁ hy₁Y) _).mp (hy₂ n hn))
      one_mem' := by
        refine ⟨Y.one_mem, fun n _ => ?_⟩
        have e : ⁅n, (1 : G)⁆ = 1 := by simp [commutatorElement_def]
        rw [e]; exact N.one_mem
      inv_mem' := by
        rintro y ⟨hyY, hy⟩
        refine ⟨Y.inv_mem hyY, fun n hn => ?_⟩
        have e : ⁅n, y⁻¹⁆ = y⁻¹ * (⁅n, y⁆)⁻¹ * (y⁻¹)⁻¹ := by
          simp only [commutatorElement_def]; group
        rw [e]
        exact (Subgroup.mem_normalizer_iff.mp (hYN y⁻¹ (Y.inv_mem hyY)) _).mp
          (N.inv_mem (hy n hn)) }
  have hAK : A ≤ K := by
    intro a ha
    refine ⟨hAY ha, fun n hn => ?_⟩
    obtain ⟨h1, h2⟩ := hcomm A hAY hN₀A n hn a ha
    have h4 : ⁅n, a⁆ ∈ L := by
      rw [S.hL]; exact Subgroup.mem_inf.mpr ⟨h1, hAbn h2⟩
    exact hLN h4
  have hAbK : Ab ≤ K := by
    intro b hb
    refine ⟨hAbY hb, fun n hn => ?_⟩
    obtain ⟨h1, h2⟩ := hcomm Ab hAbY hAbn n hn b hb
    have h4 : ⁅n, b⁆ ∈ Lb := by
      rw [S.hLb]; exact Subgroup.mem_inf.mpr ⟨h1, hN₀A h2⟩
    exact hLbN h4
  have hsAbK : conjSubgroup s Ab ≤ K := by
    intro z hz
    refine ⟨hsAbY hz, fun n hn => ?_⟩
    obtain ⟨h1, h2⟩ := hcomm (conjSubgroup s Ab) hsAbY hsAbn n hn z hz
    have h4 : s⁻¹ * ⁅n, z⁆ * s ∈ Lb := by
      rw [S.hLb]
      refine Subgroup.mem_inf.mpr ⟨mem_conjSubgroup.mp h1, ?_⟩
      exact (normalizer (A : Set G)).mul_mem
        ((normalizer (A : Set G)).mul_mem ((normalizer (A : Set G)).inv_mem hsN) (hN₀A h2)) hsN
    rw [hN]
    exact Subgroup.mem_sup_right (mem_conjSubgroup.mpr h4)
  have hYK : Y ≤ K := by
    rw [hY]
    exact sup_le (sup_le hAK hAbK) hsAbK
  intro n hn y hy
  exact (hYK hy).2 n hn

theorem sec32b_s_mem_centralizer [Finite G] {A Abar S₀ B : Subgroup G}
    (h : Sec3Ctx A Abar S₀ B) {s : G} (hs : Section3.IsSChoice A Abar S₀ B s) :
    s ∈ centralizer (A : Set G) := by
  obtain ⟨b, hb⟩ := isSChoice_iff.mp hs
  obtain ⟨hbB, _, hcase⟩ := hb
  rcases hcase with ⟨_, rfl⟩ | ⟨_, x, _, _, _, _, hsC, _⟩
  · exact h.b_le_centralizer hbB
  · exact hsC

theorem sec32b_of (h32a : Tim77Sec32aStatement) : Tim77Sec32bStatement := by
  intro G _ _ A Abar S₀ B s h hs
  obtain ⟨hNY, hYN, hNel⟩ := h32a G A Abar S₀ B s h hs
  have hY : Section3.Y A Abar s = A ⊔ Abar ⊔ conjSubgroup s Abar := by
    unfold Section3.Y; rfl
  have hN : Section3.N A Abar s = Section3.A0 A Abar ⊔ Section3.Abar0 A Abar ⊔
      conjSubgroup s (Section3.Abar0 A Abar) := by
    unfold Section3.N; rfl
  have hsyl : ∃ P : Sylow 2 G, (P : Subgroup G) ≤ normalizer (A : Set G) :=
    (sylow_le_normalizer_iff A).2 h.hyp.sylow
  have hAY : A ≤ Section3.Y A Abar s := by rw [hY]; exact le_sup_left.trans le_sup_left
  have hAbY : Abar ≤ Section3.Y A Abar s := by rw [hY]; exact le_sup_right.trans le_sup_left
  have hLN : Section3.A0 A Abar ≤ Section3.N A Abar s := by
    rw [hN]; exact le_sup_left.trans le_sup_left
  have hA := sec32b_le_normalizer h.setup h.hyp.rootTypeInCentralizer hsyl hAY hAbY hNY hLN hYN
    hNel
  refine ⟨hA, ?_⟩
  exact sec32b_commutator_le h.setup (sec32b_s_mem_centralizer h hs) hY hN hYN
    (fun y hy n hn => (Subgroup.mem_normalizer_iff.mp
      (le_normalizer_map_subtype _ (pCore 2 ↥(Section3.Y A Abar s)) hy) n).mp hn) hA

end CFSG.RankThree.GF2n.Tim77
