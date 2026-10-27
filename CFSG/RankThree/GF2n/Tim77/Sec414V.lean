module

public import CFSG.RankThree.GF2n.Tim77.Sec414b
public import CFSG.RankThree.GF2n.Tim77.Sec414Torus
public import CFSG.StronglyEmbedded.BenderCentre
public import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.RankThree.GF2n.Tim77

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Timmesfeld.RootInvolutions Subgroup

variable {G : Type} [Group G] [Finite G]

theorem sec414t_eq_one_of_pi {A V : Subgroup G} (hAV : A ≤ V) {K : Type} [Group K]
    (π : ↥V →* K) (hAinj : ∀ a : ↥V, (a : G) ∈ A → π a = 1 → a = 1) {k x : G} (hk : k ∈ V)
    (hx : x ∈ conjSubgroup k A) (hxV : x ∈ V) (h : π ⟨x, hxV⟩ = 1) : x = 1 := by
  obtain ⟨a, ha, rfl⟩ := (mem_conjSubgroup_exists_t77 k A x).1 hx
  have e : (⟨k * a * k⁻¹, hxV⟩ : ↥V) = ⟨k, hk⟩ * ⟨a, hAV ha⟩ * ⟨k, hk⟩⁻¹ := rfl
  rw [e, map_mul, map_mul, map_inv, mul_inv_eq_one, mul_eq_left] at h
  have ha1 : a = 1 := congrArg Subtype.val (hAinj ⟨a, hAV ha⟩ ha h)
  rw [ha1]
  group

theorem sec414t_inf_ne_bot {C C' C0 C0' : Subgroup G} {f c c' : G}
    (hfC : f ∈ normalizer (C : Set G)) (hfC' : f ∈ normalizer (C' : Set G))
    (hcC : c ∈ C) (hcC' : c' ∈ C') (hfc : f * c = c * f → c ∈ C0)
    (hfc' : f * c' = c' * f → c' ∈ C0') (hc0 : c ∉ C0) (hc0' : c' ∉ C0')
    (hcc' : f * (c * c') = c * c' * f) (hcomm : Sec414Comm C C') : C ⊓ C' ≠ ⊥ := by
  set u : G := f * c * f⁻¹ with hu
  set u' : G := f * c' * f⁻¹ with hu'
  have huC : u ∈ C := (Subgroup.mem_normalizer_iff.mp hfC c).mp hcC
  have hu'C' : u' ∈ C' := (Subgroup.mem_normalizer_iff.mp hfC' c').mp hcC'
  have h₁C : c⁻¹ * u ∈ C := C.mul_mem (C.inv_mem hcC) huC
  have h₂C' : c'⁻¹ * u' ∈ C' := C'.mul_mem (C'.inv_mem hcC') hu'C'
  have h₁1 : c⁻¹ * u ≠ 1 := by
    intro h
    apply hc0
    apply hfc
    have : f * c * f⁻¹ = c := (inv_mul_eq_one.mp h).symm
    calc f * c = f * c * f⁻¹ * f := by group
      _ = c * f := by rw [this]
  have huu : u * u' = c * c' := by
    calc u * u' = f * (c * c') * f⁻¹ := by rw [hu, hu']; group
      _ = c * c' := by rw [hcc']; group
  have hkey : (c⁻¹ * u) * (c'⁻¹ * u') = 1 := by
    have hc1 : (c⁻¹ * u) * c'⁻¹ = c'⁻¹ * (c⁻¹ * u) :=
      hcomm _ h₁C _ (C'.inv_mem hcC')
    calc (c⁻¹ * u) * (c'⁻¹ * u') = ((c⁻¹ * u) * c'⁻¹) * u' := by group
      _ = (c'⁻¹ * (c⁻¹ * u)) * u' := by rw [hc1]
      _ = c'⁻¹ * c⁻¹ * (u * u') := by group
      _ = 1 := by rw [huu]; group
  have h₁C' : c⁻¹ * u ∈ C' := by
    have : c⁻¹ * u = (c'⁻¹ * u')⁻¹ := eq_inv_of_mul_eq_one_left hkey
    rw [this]
    exact C'.inv_mem h₂C'
  intro hbot
  apply h₁1
  have : c⁻¹ * u ∈ C ⊓ C' := ⟨h₁C, h₁C'⟩
  rw [hbot] at this
  exact this

theorem sec414t_normalizes {A A0 TG : Subgroup G} {n k a₀ z : G} (S : Sec414Sys A A0)
    (hpartner : ∀ P : Subgroup G, IsPGroup 2 P → P ≤ centralizer (A : Set G) →
      ∃ f : G, f ∈ normalizer (A : Set G) ∧ f ≠ 1 ∧ f * f = 1 ∧
        ∀ k : G, conjSubgroup k A ≤ P → f ∈ normalizer (conjSubgroup k A : Set G) ∧
          ∀ x ∈ conjSubgroup k A, (f * x = x * f ↔ x ∈ conjSubgroup k A0))
    (hTG : IsPGroup 2 TG) (hA : A ≤ TG) (hAn : conjSubgroup n A ≤ TG)
    (hC : conjSubgroup k A ≤ TG) (hCn : conjSubgroup (n * k) A ≤ TG)
    (ha₀ : a₀ ∈ A0) (hz2 : z * z = 1) (hnz : n * z * n⁻¹ = z)
    (hzn : z * (n * a₀ * n⁻¹) = n * a₀ * n⁻¹ * z)
    (hc : a₀ * z ∈ conjSubgroup k A) (hc0 : a₀ * z ∉ conjSubgroup k A0) :
    n ∈ normalizer (conjSubgroup k A : Set G) := by
  have hcomm : ∀ g h : G, conjSubgroup g A ≤ TG → conjSubgroup h A ≤ TG →
      Sec414Comm (conjSubgroup g A) (conjSubgroup h A) :=
    fun g h hg hh => S.comm_of_isPGroup_conj g h (hTG.to_le (sup_le hg hh))
  have hA1 : conjSubgroup (1 : G) A ≤ TG := by rwa [conjSubgroup_one]
  have hAAn : Sec414Comm A (conjSubgroup n A) := by
    have := hcomm 1 n hA1 hAn
    rwa [conjSubgroup_one] at this
  have hAC : Sec414Comm A (conjSubgroup k A) := by
    have := hcomm 1 k hA1 hC
    rwa [conjSubgroup_one] at this
  have hACn : Sec414Comm A (conjSubgroup (n * k) A) := by
    have := hcomm 1 (n * k) hA1 hCn
    rwa [conjSubgroup_one] at this
  have hCCn : Sec414Comm (conjSubgroup k A) (conjSubgroup (n * k) A) := hcomm k (n * k) hC hCn
  set P : Subgroup G :=
    A ⊔ conjSubgroup n A ⊔ conjSubgroup k A ⊔ conjSubgroup (n * k) A with hP
  have hPTG : P ≤ TG := sup_le (sup_le (sup_le hA hAn) hC) hCn
  have hcent : ∀ X : Subgroup G, Sec414Comm A X → X ≤ centralizer (A : Set G) :=
    fun X hX x hx => Subgroup.mem_centralizer_iff.mpr fun a ha => hX a ha x hx
  have hPA : P ≤ centralizer (A : Set G) :=
    sup_le (sup_le (sup_le (hcent A fun a ha b hb => S.comm_A ha hb) (hcent _ hAAn))
      (hcent _ hAC)) (hcent _ hACn)
  obtain ⟨f, -, -, -, hf⟩ := hpartner P (hTG.to_le hPTG) hPA
  have hAP : conjSubgroup (1 : G) A ≤ P := by
    rw [conjSubgroup_one]
    exact le_sup_left.trans (le_sup_left.trans le_sup_left)
  have hAnP : conjSubgroup n A ≤ P := le_sup_right.trans (le_sup_left.trans le_sup_left)
  have hCP : conjSubgroup k A ≤ P := le_sup_right.trans le_sup_left
  have hCnP : conjSubgroup (n * k) A ≤ P := le_sup_right
  obtain ⟨-, hf1⟩ := hf 1 hAP
  obtain ⟨-, hfn⟩ := hf n hAnP
  obtain ⟨hfC, hfk⟩ := hf k hCP
  obtain ⟨hfCn, hfnk⟩ := hf (n * k) hCnP
  have ha₀A : a₀ ∈ A := S.a0_le ha₀
  have hfa₀ : f * a₀ = a₀ * f :=
    (hf1 a₀ (by rw [conjSubgroup_one]; exact ha₀A)).mpr (by rw [conjSubgroup_one]; exact ha₀)
  have hfa₀n : f * (n * a₀ * n⁻¹) = n * a₀ * n⁻¹ * f :=
    (hfn _ ((mem_conjSubgroup_conj_t77 n a₀ A).2 ha₀A)).mpr
      ((mem_conjSubgroup_conj_t77 n a₀ A0).2 ha₀)
  have hc' : n * (a₀ * z) * n⁻¹ ∈ conjSubgroup (n * k) A := by
    rw [conjSubgroup_mul]
    exact (mem_conjSubgroup_conj_t77 n _ _).2 hc
  have hc0' : n * (a₀ * z) * n⁻¹ ∉ conjSubgroup (n * k) A0 := by
    rw [conjSubgroup_mul]
    exact fun h => hc0 ((mem_conjSubgroup_conj_t77 n _ _).1 h)
  have hprod : a₀ * z * (n * (a₀ * z) * n⁻¹) = a₀ * (n * a₀ * n⁻¹) := by
    have e : n * (a₀ * z) * n⁻¹ = n * a₀ * n⁻¹ * (n * z * n⁻¹) := by group
    rw [e, hnz]
    calc a₀ * z * (n * a₀ * n⁻¹ * z) = a₀ * (z * (n * a₀ * n⁻¹)) * z := by group
      _ = a₀ * (n * a₀ * n⁻¹) * (z * z) := by rw [hzn]; group
      _ = a₀ * (n * a₀ * n⁻¹) := by rw [hz2, mul_one]
  have hfcc' : f * (a₀ * z * (n * (a₀ * z) * n⁻¹)) = a₀ * z * (n * (a₀ * z) * n⁻¹) * f := by
    rw [hprod]
    calc f * (a₀ * (n * a₀ * n⁻¹)) = (f * a₀) * (n * a₀ * n⁻¹) := by group
      _ = a₀ * (f * (n * a₀ * n⁻¹)) := by rw [hfa₀]; group
      _ = a₀ * (n * a₀ * n⁻¹) * f := by rw [hfa₀n]; group
  have hne : conjSubgroup k A ⊓ conjSubgroup n (conjSubgroup k A) ≠ ⊥ := by
    rw [← conjSubgroup_mul]
    exact sec414t_inf_ne_bot hfC hfCn hc hc' ((hfk _ hc).mp) ((hfnk _ hc').mp) hc0 hc0' hfcc' hCCn
  exact conjSubgroup_eq_self_iff.mp (conjSubgroup_eq_of_isTI (S.conj k).ti hne)

theorem sec414t_contra_of_le {A A0 V : Subgroup G} {k a₀ z : G} (S : Sec414Sys A A0)
    (hpartner : ∀ P : Subgroup G, IsPGroup 2 P → P ≤ centralizer (A : Set G) →
      ∃ f : G, f ∈ normalizer (A : Set G) ∧ f ≠ 1 ∧ f * f = 1 ∧
        ∀ k : G, conjSubgroup k A ≤ P → f ∈ normalizer (conjSubgroup k A : Set G) ∧
          ∀ x ∈ conjSubgroup k A, (f * x = x * f ↔ x ∈ conjSubgroup k A0))
    (hAV : A ≤ V) {K : Type} [Group K] (hK : CFSG.BenderSuzuki.IsBenderGroup K)
    (π : ↥V →* K) (hπ : Function.Surjective π)
    (hAinj : ∀ a : ↥V, (a : G) ∈ A → π a = 1 → a = 1)
    (ha₀ : a₀ ∈ A0) (hk : k ∈ V) (hz2 : z * z = 1) (hzc : ∀ v ∈ V, z * v = v * z)
    (hC : a₀ * z ∈ conjSubgroup k A) (hC0 : a₀ * z ∉ conjSubgroup k A0)
    (hAC : Sec414Comm A (conjSubgroup k A)) : False := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite K := Finite.of_surjective π hπ
  have hCV : conjSubgroup k A ≤ V := fun y hy => by
    obtain ⟨a, ha, rfl⟩ := (mem_conjSubgroup_exists_t77 k A y).1 hy
    exact V.mul_mem (V.mul_mem hk (hAV ha)) (V.inv_mem hk)
  have hACV : A ⊔ conjSubgroup k A ≤ V := sup_le hAV hCV
  have hAC2 : IsPGroup 2 ↥(A ⊔ conjSubgroup k A) :=
    sec414_isPGroup_sup S.elem.isPGroup (isElemAbelian_conj S.elem k).isPGroup
      fun q hq p hp => by rw [← hAC p hp q hq, mul_inv_cancel_right]; exact hp
  have hAC2' : IsPGroup 2 ((A ⊔ conjSubgroup k A).subgroupOf V) := hAC2.comap_subtype
  obtain ⟨T0, hT0⟩ := IsPGroup.exists_le_sylow hAC2'
  have hT : IsPGroup 2 (T0 : Subgroup ↥V) := T0.isPGroup'
  have hTmax : ∀ T' : Subgroup ↥V, IsPGroup 2 T' → (T0 : Subgroup ↥V) ≤ T' →
      T' = (T0 : Subgroup ↥V) := fun T' hT' hle => T0.is_maximal' hT' hle
  obtain ⟨n, hnN, -, -, htrans⟩ := sec414_exists_torus hK π hπ _ hT hTmax
  set T : Subgroup ↥V := (T0 : Subgroup ↥V) with hTdef
  set TG : Subgroup G := T.map V.subtype with hTG
  have hTG2 : IsPGroup 2 TG := hT.map V.subtype
  have hACTG : A ⊔ conjSubgroup k A ≤ TG := fun x hx =>
    ⟨⟨x, hACV hx⟩, hT0 (Subgroup.mem_subgroupOf.mpr hx), rfl⟩
  have hnTG : ∀ x ∈ TG, (n : G) * x * (n : G)⁻¹ ∈ TG := by
    rintro _ ⟨t, ht, rfl⟩
    exact ⟨n * t * n⁻¹, (Subgroup.mem_normalizer_iff.mp hnN _).mp ht, by simp⟩
  have hconj : ∀ X : Subgroup G, X ≤ TG → conjSubgroup (n : G) X ≤ TG := fun X hX x hx => by
    obtain ⟨y, hy, rfl⟩ := (mem_conjSubgroup_exists_t77 _ X x).1 hx
    exact hnTG y (hX hy)
  have hnV : (n : G) ∈ V := n.2
  have hnz : (n : G) * z * (n : G)⁻¹ = z := by
    rw [← hzc _ hnV, mul_inv_cancel_right]
  have hzn : z * ((n : G) * a₀ * (n : G)⁻¹) = (n : G) * a₀ * (n : G)⁻¹ * z :=
    hzc _ (V.mul_mem (V.mul_mem hnV (hAV (S.a0_le ha₀))) (V.inv_mem hnV))
  have hCTG : conjSubgroup k A ≤ TG := le_sup_right.trans hACTG
  have hnC : (n : G) ∈ normalizer (conjSubgroup k A : Set G) :=
    sec414t_normalizes S hpartner hTG2 (le_sup_left.trans hACTG)
      (hconj A (le_sup_left.trans hACTG)) hCTG
      (by rw [conjSubgroup_mul]; exact hconj _ hCTG) ha₀ hz2 hnz hzn hC hC0
  have hnC0 : ∀ i : ℕ, ∀ x ∈ conjSubgroup k A0,
      (n : G) ^ i * x * ((n : G) ^ i)⁻¹ ∈ conjSubgroup k A0 := fun i x hx =>
    (S.conj k).a0_norm _ (Subgroup.pow_mem _ hnC i) x hx
  obtain ⟨⟨x₀, hx₀⟩, hx₀1'⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp (S.conj k).a0_ne
  have hx₀1 : x₀ ≠ 1 := fun e => hx₀1' (Subtype.ext e)
  have hx₀C : x₀ ∈ conjSubgroup k A := (S.conj k).a0_le hx₀
  obtain ⟨Sy, hSy⟩ : ∃ Sy : Sylow 2 K, (Sy : Subgroup K) = T.map π :=
    ⟨Sylow.mapSurjective hπ T0, rfl⟩
  have hcenter : ∀ E : Subgroup K, E ≤ T.map π → (∀ x ∈ E, x * x = 1) →
      E ≤ CFSG.ComponentClassification.AschbacherToolkit.Bender.sylowCenter (T.map π) := by
    intro E hE hsq
    have := CFSG.StronglyEmbedded.BenderCentre.le_sylowCenter_of_sq_eq_one hK (S := Sy) (E := E)
      (hSy ▸ hE) hsq
    rwa [hSy] at this
  have hCAC : conjSubgroup k A ≤ A ⊔ conjSubgroup k A := le_sup_right
  have hCT : (conjSubgroup k A).subgroupOf V ≤ T := fun x hx =>
    hT0 (Subgroup.mem_subgroupOf.mpr (hCAC (Subgroup.mem_subgroupOf.mp hx)))
  have hCsc : ((conjSubgroup k A).subgroupOf V).map π ≤
      CFSG.ComponentClassification.AschbacherToolkit.Bender.sylowCenter (T.map π) := by
    refine hcenter _ (Subgroup.map_mono hCT) ?_
    rintro _ ⟨y, hy, rfl⟩
    rw [← map_mul]
    have : y * y = 1 := Subtype.ext ((S.conj k).sq_A (Subgroup.mem_subgroupOf.mp hy))
    rw [this, map_one]
  have hmem : ∀ x (hx : x ∈ conjSubgroup k A), π ⟨x, hCV hx⟩ ∈
      CFSG.ComponentClassification.AschbacherToolkit.Bender.sylowCenter (T.map π) :=
    fun x hx => hCsc (Subgroup.mem_map.mpr ⟨⟨x, hCV hx⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩)
  have hne1 : ∀ x (hx : x ∈ conjSubgroup k A), x ≠ 1 → π ⟨x, hCV hx⟩ ≠ 1 :=
    fun x hx hx1 h => hx1 (sec414t_eq_one_of_pi hAV π hAinj hk hx (hCV hx) h)
  have hcC1 : a₀ * z ≠ 1 := fun h => hC0 (h ▸ (conjSubgroup k A0).one_mem)
  obtain ⟨i, hi⟩ := htrans _ (hmem x₀ hx₀C) (hne1 x₀ hx₀C hx₀1) _ (hmem _ hC) (hne1 _ hC hcC1)
  have hyC0 := hnC0 i x₀ hx₀
  have hyC : (n : G) ^ i * x₀ * ((n : G) ^ i)⁻¹ ∈ conjSubgroup k A := (S.conj k).a0_le hyC0
  have hyV : (n : G) ^ i * x₀ * ((n : G) ^ i)⁻¹ ∈ V := hCV hyC
  have hπy : π ⟨(n : G) ^ i * x₀ * ((n : G) ^ i)⁻¹, hyV⟩ = π ⟨a₀ * z, hCV hC⟩ := by
    have e : (⟨(n : G) ^ i * x₀ * ((n : G) ^ i)⁻¹, hyV⟩ : ↥V) =
        n ^ i * ⟨x₀, hCV hx₀C⟩ * (n ^ i)⁻¹ := by
      apply Subtype.ext
      simp
    rw [e]
    simp only [map_mul, map_pow, map_inv]
    exact hi
  have hq : (n : G) ^ i * x₀ * ((n : G) ^ i)⁻¹ * (a₀ * z)⁻¹ ∈ conjSubgroup k A :=
    (conjSubgroup k A).mul_mem hyC ((conjSubgroup k A).inv_mem hC)
  have hq1 := sec414t_eq_one_of_pi hAV π hAinj hk hq (hCV hq) (by
    have e : (⟨(n : G) ^ i * x₀ * ((n : G) ^ i)⁻¹ * (a₀ * z)⁻¹, hCV hq⟩ : ↥V) =
        ⟨(n : G) ^ i * x₀ * ((n : G) ^ i)⁻¹, hyV⟩ * ⟨a₀ * z, hCV hC⟩⁻¹ := rfl
    rw [e, map_mul, map_inv, hπy, mul_inv_cancel])
  apply hC0
  have : (n : G) ^ i * x₀ * ((n : G) ^ i)⁻¹ = a₀ * z := mul_inv_eq_one.mp hq1
  rw [← this]
  exact hyC0

theorem sec414t_contra {A A0 : Subgroup G} {g : G} (S : Sec414Sys A A0)
    (hpartner : ∀ P : Subgroup G, IsPGroup 2 P → P ≤ centralizer (A : Set G) →
      ∃ f : G, f ∈ normalizer (A : Set G) ∧ f ≠ 1 ∧ f * f = 1 ∧
        ∀ k : G, conjSubgroup k A ≤ P → f ∈ normalizer (conjSubgroup k A : Set G) ∧
          ∀ x ∈ conjSubgroup k A, (f * x = x * f ↔ x ∈ conjSubgroup k A0))
    {K : Type} [Group K] (hK : CFSG.BenderSuzuki.IsBenderGroup K)
    (π : ↥(A ⊔ conjSubgroup g A) →* K) (hπ : Function.Surjective π)
    (hAinj : ∀ a : ↥(A ⊔ conjSubgroup g A), (a : G) ∈ A → π a = 1 → a = 1)
    {a₀ z k : G} (ha₀ : a₀ ∈ A0) (hk : k ∈ A ⊔ conjSubgroup g A) (hz2 : z * z = 1)
    (hzc : ∀ v ∈ A ⊔ conjSubgroup g A, z * v = v * z)
    (hC : a₀ * z ∈ conjSubgroup k A) (hC0 : a₀ * z ∉ conjSubgroup k A0)
    (hAC : Sec414Comm A (conjSubgroup k A)) : False :=
  sec414t_contra_of_le S hpartner le_sup_left hK π hπ hAinj ha₀ hk hz2 hzc hC hC0 hAC

end CFSG.RankThree.GF2n.Tim77
