module

public import CFSG.Open.Defs
public import CFSG.Assembly.Subnormal
public import CFSG.GroupTheory.LocalCores.Layer.CentralExtension
public import CFSG.GroupTheory.LocalCores.Fitting

public section

namespace CFSG.StandardType.TableCRes

open CFSG.Open

theorem isSubnormal_of_normal_trans {G : Type*} [Group G] {H N T : Subgroup G}
    (hH : IsSubnormal H N) (hNT : N ≤ T) (hN : (N.subgroupOf T).Normal) :
    IsSubnormal H T := by
  revert hNT hN
  induction hH with
  | refl _ => exact fun hNT hN => IsSubnormal.step hNT hN (IsSubnormal.refl T)
  | step hHM hNorm _ ih => exact fun hNT hN => IsSubnormal.step hHM hNorm (ih hNT hN)

theorem isComponentOf_subgroupOf_of_le {Γ : Type*} [Group Γ] {Q H G : Subgroup Γ}
    (hQ : IsComponentOf Q H) (hQG : Q ≤ G) :
    IsComponentOf (Q.subgroupOf G) (H.subgroupOf G) :=
  ⟨Subgroup.comap_mono hQ.1, hQ.2.1.comap G.subtype,
    CFSG.Open.IsQuasisimple.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hQG) hQ.2.2⟩

theorem isComponentOf_map_injective {X Y : Type*} [Group X] [Group Y] (f : X →* Y)
    (hf : Function.Injective f) {L K : Subgroup X} (h : IsComponentOf L K) :
    IsComponentOf (L.map f) (K.map f) :=
  ⟨Subgroup.map_mono h.1, h.2.1.map f,
    CFSG.Open.IsQuasisimple.of_mulEquiv (L.equivMapOfInjective f hf).symm
    h.2.2⟩

@[expose] noncomputable def centerQuotMulEquivOfEquiv {A A' : Type*} [Group A] [Group A']
    (a : A ≃* A') :
    A ⧸ Subgroup.center A ≃* A' ⧸ Subgroup.center A' :=
  QuotientGroup.congr _ _ a (Subgroup.map_center_eq a)

theorem centerQuot_equiv_map_central {G : Type*} [Group G] {Z : Subgroup G} [Z.Normal]
    (hZ : Z ≤ Subgroup.center G) {J : Subgroup G} (hPerf : Group.IsPerfect ↥J) :
    Nonempty (↥J ⧸ Subgroup.center ↥J ≃* ↥(J.map (QuotientGroup.mk' Z)) ⧸
      Subgroup.center ↥(J.map (QuotientGroup.mk' Z))) := by
  set f : ↥J →* ↥(J.map (QuotientGroup.mk' Z)) := (QuotientGroup.mk' Z).subgroupMap J
  have hf : Function.Surjective f := MonoidHom.subgroupMap_surjective _ J
  have hker : f.ker ≤ Subgroup.center ↥J := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have hx1 : ((x : G) : G ⧸ Z) = 1 := congrArg Subtype.val hx
    have hxZ : (x : G) ∈ Z := (QuotientGroup.eq_one_iff (x : G)).mp hx1
    refine Subgroup.mem_center_iff.mpr fun g => Subtype.ext ?_
    exact Subgroup.mem_center_iff.mp (hZ hxZ) (g : G)
  have hc : Subgroup.center ↥J =
      ((QuotientGroup.mk' (Subgroup.center ↥(J.map (QuotientGroup.mk' Z)))).comp f).ker := by
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk',
      CFSG.LocalCores.comap_center_eq_of_perfect hPerf f hf hker]
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hc).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ ((QuotientGroup.mk'_surjective _).comp hf))⟩

theorem isComponentOf_map_central {G : Type*} [Group G] {Z : Subgroup G} [Z.Normal]
    (hZ : Z ≤ Subgroup.center G) {C : Subgroup G} {T : Subgroup (G ⧸ Z)}
    (hCT : C.map (QuotientGroup.mk' Z) ≤ T)
    (hN : ((C.map (QuotientGroup.mk' Z)).subgroupOf T).Normal) {J : Subgroup G}
    (hJ : IsComponentOf J C) : IsComponentOf (J.map (QuotientGroup.mk' Z)) T := by
  unfold CFSG.Open.IsComponentOf CFSG.Open.IsQuasisimple at hJ ⊢
  obtain ⟨hJC, hJsub, hJcomm, hJsimp⟩ := hJ
  have hPerf : Group.IsPerfect ↥J := Group.isPerfect_def.mpr hJcomm
  obtain ⟨e⟩ := centerQuot_equiv_map_central hZ hPerf
  have hQperf : Group.IsPerfect ↥(J.map (QuotientGroup.mk' Z)) :=
    Group.IsPerfect.ofSurjective (MonoidHom.subgroupMap_surjective (QuotientGroup.mk' Z) J)
  exact ⟨(Subgroup.map_mono hJC).trans hCT,
    isSubnormal_of_normal_trans (hJsub.map (QuotientGroup.mk' Z)) hCT hN,
    Group.isPerfect_def.mp hQperf, e.symm.isSimpleGroup⟩

theorem isComponentOf_map_centralizer_central {G : Type*} [Group G] {Z : Subgroup G} [Z.Normal]
    (hZ : Z ≤ Subgroup.center G) (N : Set G) {J : Subgroup G}
    (hJ : IsComponentOf J (Subgroup.centralizer N)) :
    IsComponentOf (J.map (QuotientGroup.mk' Z))
      (Subgroup.centralizer ((QuotientGroup.mk' Z) '' N)) := by
  have hCT : (Subgroup.centralizer N).map (QuotientGroup.mk' Z) ≤
      Subgroup.centralizer ((QuotientGroup.mk' Z) '' N) := by
    rintro _ ⟨y, hy, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨n, hn, rfl⟩
    rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.mp hy n hn]
  refine isComponentOf_map_central hZ hCT ?_ hJ
  rw [Subgroup.normal_subgroupOf_iff hCT]
  rintro h k ⟨y, hy, rfl⟩ hk
  obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective k
  refine Subgroup.mem_map.mpr ⟨z * y * z⁻¹, ?_, ?_⟩
  · rw [Subgroup.mem_centralizer_iff]
    intro n hn
    have hkn : QuotientGroup.mk' Z n * QuotientGroup.mk' Z z =
        QuotientGroup.mk' Z z * QuotientGroup.mk' Z n :=
      Subgroup.mem_centralizer_iff.mp hk _ ⟨n, hn, rfl⟩
    rw [← map_mul, ← map_mul] at hkn
    have hu : (n * z)⁻¹ * (z * n) ∈ Z := QuotientGroup.eq.mp hkn
    obtain ⟨u, hu_c, hm⟩ : ∃ u ∈ Subgroup.center G, z⁻¹ * n * z = n * u⁻¹ :=
      ⟨(n * z)⁻¹ * (z * n), hZ hu, by group⟩
    have hyu : y * u⁻¹ = u⁻¹ * y :=
      Subgroup.mem_center_iff.mp ((Subgroup.center G).inv_mem hu_c) y
    have hny : n * y = y * n := Subgroup.mem_centralizer_iff.mp hy n hn
    have key : (z⁻¹ * n * z) * y = y * (z⁻¹ * n * z) := by
      rw [hm]
      calc n * u⁻¹ * y = n * (u⁻¹ * y) := by rw [mul_assoc]
        _ = n * (y * u⁻¹) := by rw [hyu]
        _ = n * y * u⁻¹ := by rw [mul_assoc]
        _ = y * n * u⁻¹ := by rw [hny]
        _ = y * (n * u⁻¹) := by rw [mul_assoc]
    calc n * (z * y * z⁻¹) = z * ((z⁻¹ * n * z) * y) * z⁻¹ := by group
      _ = z * (y * (z⁻¹ * n * z)) * z⁻¹ := by rw [key]
      _ = z * y * z⁻¹ * n := by group
  · simp [map_mul, map_inv]

theorem map_centralizer_of_injective_range {G H : Type*} [Group G] [Group H] (φ : G →* H)
    (hφ : Function.Injective φ) (S : Subgroup G) :
    (Subgroup.centralizer (S : Set G)).map φ =
      φ.range ⊓ Subgroup.centralizer ((S.map φ : Subgroup H) : Set H) := by
  ext x
  rw [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨⟨y, rfl⟩, ?_⟩
    rintro _ ⟨s, hs, rfl⟩
    rw [← map_mul, ← map_mul]
    exact congrArg φ ((Subgroup.mem_centralizer_iff.1 hy) s hs)
  · rintro ⟨⟨y, rfl⟩, h⟩
    refine ⟨y, Subgroup.mem_centralizer_iff.2 fun s hs => hφ ?_, rfl⟩
    rw [map_mul, map_mul]
    exact h (φ s) ⟨s, hs, rfl⟩

private theorem eq_of_conj_eq_of_center_eq_bot {Q : Type*} [Group Q]
    (hc : Subgroup.center Q = ⊥) {u v : Q} (h : ∀ w : Q, u * w * u⁻¹ = v * w * v⁻¹) :
    u = v := by
  have key : ∀ g : Q, v⁻¹ * u * g = g * (v⁻¹ * u) := by
    intro g
    calc v⁻¹ * u * g = v⁻¹ * (u * g * u⁻¹) * u := by group
      _ = v⁻¹ * (v * g * v⁻¹) * u := by rw [h g]
      _ = g * (v⁻¹ * u) := by group
  have hz : v⁻¹ * u ∈ Subgroup.center Q :=
    Subgroup.mem_center_iff.mpr (fun g => (key g).symm)
  rw [hc, Subgroup.mem_bot, inv_mul_eq_one] at hz
  exact hz.symm

theorem exists_inner_hom_of_faithful_inner {X : Type*} [Group X] {G₀ B : Subgroup X}
    (hBN : B ≤ Subgroup.normalizer (G₀ : Set X))
    (hin : ∀ b ∈ B, ∃ g ∈ G₀, b * g ∈ Subgroup.centralizer (G₀ : Set X))
    (hfaith : B ⊓ Subgroup.centralizer (G₀ : Set X) = ⊥)
    (hcl : Subgroup.center (↥G₀ ⧸ Subgroup.center ↥G₀) = ⊥) :
    ∃ ν : ↥B →* ↥G₀ ⧸ Subgroup.center ↥G₀, Function.Injective ν ∧
      ∀ b : ↥B, ∃ n : ↥G₀, (QuotientGroup.mk n : ↥G₀ ⧸ Subgroup.center ↥G₀) = ν b ∧
        ∀ y : ↥G₀, (b : X) * (y : X) * (b : X)⁻¹ = (n : X) * (y : X) * (n : X)⁻¹ := by
  have hmemB : ∀ (b : ↥B) (y : ↥G₀), (b : X) * (y : X) * (b : X)⁻¹ ∈ G₀ := fun b y =>
    (Subgroup.mem_set_normalizer_iff.mp (hBN b.2) (y : X)).mp y.2
  have hg : ∀ b : ↥B, ∃ g ∈ G₀, (b : X) * g ∈ Subgroup.centralizer (G₀ : Set X) :=
    fun b => hin (b : X) b.2
  choose g hgG hgC using hg
  have hmemg : ∀ (b : ↥B) (y : ↥G₀), (g b)⁻¹ * (y : X) * g b ∈ G₀ := fun b y =>
    G₀.mul_mem (G₀.mul_mem (G₀.inv_mem (hgG b)) y.2) (hgG b)
  have hconjX : ∀ (b : ↥B) (y : ↥G₀),
      (b : X) * (y : X) * (b : X)⁻¹ = (g b)⁻¹ * (y : X) * g b := by
    intro b y
    have E : ((g b)⁻¹ * (y : X) * g b) * ((b : X) * g b)
        = ((b : X) * g b) * ((g b)⁻¹ * (y : X) * g b) :=
      Subgroup.mem_centralizer_iff.mp (hgC b) ((g b)⁻¹ * (y : X) * g b) (hmemg b y)
    have E2 : ((g b)⁻¹ * (y : X) * g b * (b : X)) * g b = ((b : X) * (y : X)) * g b := by
      calc ((g b)⁻¹ * (y : X) * g b * (b : X)) * g b
          = ((g b)⁻¹ * (y : X) * g b) * ((b : X) * g b) := by group
        _ = ((b : X) * g b) * ((g b)⁻¹ * (y : X) * g b) := E
        _ = ((b : X) * (y : X)) * g b := by group
    have E3 : (g b)⁻¹ * (y : X) * g b * (b : X) = (b : X) * (y : X) := mul_right_cancel E2
    rw [← E3]
    group
  obtain ⟨ν₀, hν₀⟩ : ∃ f : ↥B → ↥G₀ ⧸ Subgroup.center ↥G₀,
      ∀ b, f b = (QuotientGroup.mk (⟨g b, hgG b⟩ : ↥G₀))⁻¹ :=
    ⟨fun b => (QuotientGroup.mk (⟨g b, hgG b⟩ : ↥G₀))⁻¹, fun b => rfl⟩
  have hkey : ∀ (b : ↥B) (y : ↥G₀) (hy : (b : X) * (y : X) * (b : X)⁻¹ ∈ G₀),
      (QuotientGroup.mk (⟨(b : X) * (y : X) * (b : X)⁻¹, hy⟩ : ↥G₀) :
        ↥G₀ ⧸ Subgroup.center ↥G₀) = ν₀ b * QuotientGroup.mk y * (ν₀ b)⁻¹ := by
    intro b y hy
    have hel : (⟨(b : X) * (y : X) * (b : X)⁻¹, hy⟩ : ↥G₀)
        = ⟨(g b)⁻¹ * (y : X) * g b, hmemg b y⟩ := Subtype.ext (hconjX b y)
    have hprod : (⟨(g b)⁻¹ * (y : X) * g b, hmemg b y⟩ : ↥G₀)
        = (⟨g b, hgG b⟩ : ↥G₀)⁻¹ * y * (⟨g b, hgG b⟩ : ↥G₀) := by
      ext
      simp
    rw [hel, hprod, hν₀ b, inv_inv, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
      QuotientGroup.mk_inv]
  have hmul : ∀ a b : ↥B, ν₀ (a * b) = ν₀ a * ν₀ b := by
    intro a b
    have hconj : ∀ w : ↥G₀ ⧸ Subgroup.center ↥G₀,
        ν₀ (a * b) * w * (ν₀ (a * b))⁻¹ = ν₀ a * ν₀ b * w * (ν₀ a * ν₀ b)⁻¹ := by
      intro w
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective w
      calc ν₀ (a * b) * QuotientGroup.mk y * (ν₀ (a * b))⁻¹
          = (QuotientGroup.mk (⟨((a * b : ↥B) : X) * (y : X) * ((a * b : ↥B) : X)⁻¹,
              hmemB (a * b) y⟩ : ↥G₀) : ↥G₀ ⧸ Subgroup.center ↥G₀) :=
            (hkey (a * b) y (hmemB (a * b) y)).symm
        _ = (QuotientGroup.mk (⟨(a : X) * ((b : X) * (y : X) * (b : X)⁻¹) * (a : X)⁻¹,
              hmemB a ⟨(b : X) * (y : X) * (b : X)⁻¹, hmemB b y⟩⟩ : ↥G₀) :
              ↥G₀ ⧸ Subgroup.center ↥G₀) := by
            congr 1
            apply Subtype.ext
            simp only [Subgroup.coe_mul]
            group
        _ = ν₀ a * QuotientGroup.mk (⟨(b : X) * (y : X) * (b : X)⁻¹, hmemB b y⟩ : ↥G₀)
              * (ν₀ a)⁻¹ := hkey a ⟨(b : X) * (y : X) * (b : X)⁻¹, hmemB b y⟩ _
        _ = ν₀ a * (ν₀ b * QuotientGroup.mk y * (ν₀ b)⁻¹) * (ν₀ a)⁻¹ := by
            rw [hkey b y (hmemB b y)]
        _ = ν₀ a * ν₀ b * QuotientGroup.mk y * (ν₀ a * ν₀ b)⁻¹ := by group
    exact eq_of_conj_eq_of_center_eq_bot hcl hconj
  have hinj1 : ∀ b : ↥B, ν₀ b = 1 → b = 1 := by
    intro b hb
    rw [hν₀ b, inv_eq_one, QuotientGroup.eq_one_iff] at hb
    have hcg : g b ∈ Subgroup.centralizer (G₀ : Set X) := by
      refine Subgroup.mem_centralizer_iff.mpr (fun h hh => ?_)
      have hc := Subgroup.mem_center_iff.mp hb ⟨h, hh⟩
      exact congrArg (fun x : ↥G₀ => (x : X)) hc
    have hbC : (b : X) ∈ Subgroup.centralizer (G₀ : Set X) := by
      have h1 := (Subgroup.centralizer (G₀ : Set X)).mul_mem (hgC b)
        ((Subgroup.centralizer (G₀ : Set X)).inv_mem hcg)
      rwa [mul_inv_cancel_right] at h1
    have hbBot : (b : X) ∈ B ⊓ Subgroup.centralizer (G₀ : Set X) :=
      Subgroup.mem_inf.mpr ⟨b.2, hbC⟩
    rw [hfaith, Subgroup.mem_bot] at hbBot
    exact Subtype.ext (by simpa using hbBot)
  have hsurj : ∀ b : ↥B, ∃ n : ↥G₀, (QuotientGroup.mk n : ↥G₀ ⧸ Subgroup.center ↥G₀) = ν₀ b ∧
      ∀ y : ↥G₀, (b : X) * (y : X) * (b : X)⁻¹ = (n : X) * (y : X) * (n : X)⁻¹ := by
    intro b
    refine ⟨(⟨g b, hgG b⟩ : ↥G₀)⁻¹, ?_, ?_⟩
    · rw [hν₀ b, QuotientGroup.mk_inv]
    · intro y
      show (b : X) * (y : X) * (b : X)⁻¹ = (g b)⁻¹ * (y : X) * (g b)⁻¹⁻¹
      rw [inv_inv]
      exact hconjX b y
  have hinj : Function.Injective (MonoidHom.mk' ν₀ hmul) := by
    rw [injective_iff_map_eq_one]
    intro b hb
    exact hinj1 b hb
  exact ⟨MonoidHom.mk' ν₀ hmul, hinj, hsurj⟩

theorem centralizer_eq_of_inner_action {X : Type*} [Group X] {G₀ B D : Subgroup X} (hDB : D ≤ B)
    (ν : ↥B →* ↥G₀ ⧸ Subgroup.center ↥G₀)
    (hact : ∀ b : ↥B, ∃ n : ↥G₀, (QuotientGroup.mk n : ↥G₀ ⧸ Subgroup.center ↥G₀) = ν b ∧
      ∀ y : ↥G₀, (b : X) * (y : X) * (b : X)⁻¹ = (n : X) * (y : X) * (n : X)⁻¹) :
    (G₀ ⊓ Subgroup.centralizer (D : Set X)).subgroupOf G₀ =
      Subgroup.centralizer {n : ↥G₀ | ∃ d : ↥B, (d : X) ∈ D ∧
        (QuotientGroup.mk n : ↥G₀ ⧸ Subgroup.center ↥G₀) = ν d} := by
  ext y
  simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_centralizer_iff,
    Set.mem_setOf_eq, SetLike.mem_coe]
  constructor
  · rintro ⟨-, hy⟩ n ⟨d, hdD, hnd⟩
    obtain ⟨n₀, hn₀, hconj⟩ := hact d
    have h3 : (d : X) * (y : X) * (d : X)⁻¹ = (y : X) :=
      mul_inv_eq_iff_eq_mul.2 (hy (d : X) hdD)
    have h4 : (n₀ : X) * (y : X) * (n₀ : X)⁻¹ = (y : X) := (hconj y).symm.trans h3
    have h5 : (n₀ : X) * (y : X) = (y : X) * (n₀ : X) := mul_inv_eq_iff_eq_mul.1 h4
    have h6' : n₀ * y = y * n₀ := Subtype.ext h5
    have h6 : Commute n₀ y := h6'
    have hmk : (QuotientGroup.mk n : ↥G₀ ⧸ Subgroup.center ↥G₀) = QuotientGroup.mk n₀ :=
      hnd.trans hn₀.symm
    have hz : n⁻¹ * n₀ ∈ Subgroup.center ↥G₀ := QuotientGroup.eq.1 hmk
    have hzy : Commute (n⁻¹ * n₀) y := (Subgroup.mem_center_iff.1 hz y).symm
    have hnn : Commute (n₀ * (n⁻¹ * n₀)⁻¹) y := h6.mul_left hzy.inv_left
    have hid : n₀ * (n⁻¹ * n₀)⁻¹ = n := by
      rw [mul_inv_rev, inv_inv, mul_inv_cancel_left]
    rw [hid] at hnn
    exact hnn.eq
  · intro hy
    refine ⟨y.2, fun d hdD => ?_⟩
    obtain ⟨n₀, hn₀, hconj⟩ := hact ⟨d, hDB hdD⟩
    have hcomm : n₀ * y = y * n₀ := hy n₀ ⟨⟨d, hDB hdD⟩, hdD, hn₀⟩
    have h1 : (n₀ : X) * (y : X) = (y : X) * (n₀ : X) := congrArg Subtype.val hcomm
    have h2 : d * (y : X) * d⁻¹ = (n₀ : X) * (y : X) * (n₀ : X)⁻¹ := hconj y
    have h3 : d * (y : X) * d⁻¹ = (y : X) := h2.trans (mul_inv_eq_iff_eq_mul.2 h1)
    exact mul_inv_eq_iff_eq_mul.1 h3

theorem image_eq_of_inner_action {X : Type*} [Group X] {G₀ B D : Subgroup X}
    (ν : ↥B →* ↥G₀ ⧸ Subgroup.center ↥G₀)
    (hact : ∀ b : ↥B, ∃ n : ↥G₀, (QuotientGroup.mk n : ↥G₀ ⧸ Subgroup.center ↥G₀) = ν b ∧
      ∀ y : ↥G₀, (b : X) * (y : X) * (b : X)⁻¹ = (n : X) * (y : X) * (n : X)⁻¹) :
    (QuotientGroup.mk' (Subgroup.center ↥G₀)) ''
        {n : ↥G₀ | ∃ d : ↥B, (d : X) ∈ D ∧
          (QuotientGroup.mk n : ↥G₀ ⧸ Subgroup.center ↥G₀) = ν d} =
      ((D.subgroupOf B).map ν : Subgroup (↥G₀ ⧸ Subgroup.center ↥G₀)) := by
  ext q
  constructor
  · rintro ⟨n, ⟨d, hdD, hnd⟩, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_map]
    refine ⟨d, Subgroup.mem_subgroupOf.2 hdD, ?_⟩
    rw [QuotientGroup.mk'_apply]
    exact hnd.symm
  · intro hq
    rw [SetLike.mem_coe, Subgroup.mem_map] at hq
    obtain ⟨d, hd, rfl⟩ := hq
    obtain ⟨n₀, hn₀, -⟩ := hact d
    refine ⟨n₀, ⟨d, Subgroup.mem_subgroupOf.1 hd, hn₀⟩, ?_⟩
    rw [QuotientGroup.mk'_apply]
    exact hn₀

private lemma commutator_map_mul_aux {G : Type*} [Group G] {n x y : G}
    (hy : ∀ g : G, g * (n * y * n⁻¹ * y⁻¹) = (n * y * n⁻¹ * y⁻¹) * g) :
    n * (x * y) * n⁻¹ * (x * y)⁻¹ = (n * x * n⁻¹ * x⁻¹) * (n * y * n⁻¹ * y⁻¹) := by
  have hzx : (n * y * n⁻¹ * y⁻¹) * x = x * (n * y * n⁻¹ * y⁻¹) := (hy x).symm
  have h : (n * x * n⁻¹ * x⁻¹) * (n * y * n⁻¹ * y⁻¹) * x
      = n * (x * y) * n⁻¹ * (x * y)⁻¹ * x := by
    calc (n * x * n⁻¹ * x⁻¹) * (n * y * n⁻¹ * y⁻¹) * x
        = (n * x * n⁻¹ * x⁻¹) * ((n * y * n⁻¹ * y⁻¹) * x) := by group
      _ = (n * x * n⁻¹ * x⁻¹) * (x * (n * y * n⁻¹ * y⁻¹)) := by rw [hzx]
      _ = n * x * n⁻¹ * (n * y * n⁻¹ * y⁻¹) := by group
      _ = n * (x * y) * n⁻¹ * (x * y)⁻¹ * x := by group
  exact (mul_right_cancel h).symm

theorem commute_of_perfect_central_commutators {G : Type*} [Group G] {J : Subgroup G}
    (hJ : commutator ↥J = ⊤) {n : G} (hn : ∀ j ∈ J, n * j * n⁻¹ * j⁻¹ ∈ Subgroup.center G) :
    ∀ j ∈ J, n * j = j * n := by
  let f : ↥J → ↥(Subgroup.center G) := fun j =>
    ⟨n * (j : G) * n⁻¹ * (j : G)⁻¹, hn (j : G) j.2⟩
  have hmul : ∀ a b : ↥J, f (a * b) = f a * f b := by
    intro a b
    apply Subtype.ext
    have hy := Subgroup.mem_center_iff.mp (hn (b : G) b.2)
    exact commutator_map_mul_aux (x := (a : G)) (y := (b : G)) hy
  let cmap : ↥J →* ↥(Subgroup.center G) := MonoidHom.mk' f hmul
  have hker : commutator ↥J ≤ cmap.ker := by
    refine Subgroup.commutator_le.mpr ?_
    intro g₁ _ g₂ _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact mul_comm' (cmap g₁) (cmap g₂)
  intro j hj
  have htop : (⟨j, hj⟩ : ↥J) ∈ commutator ↥J := by
    rw [hJ]
    exact Subgroup.mem_top _
  have hone : cmap ⟨j, hj⟩ = 1 := hker htop
  have h1 : n * j * n⁻¹ * j⁻¹ = 1 := congrArg Subtype.val hone
  rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h1
  exact h1

theorem commute_of_inner_action_on_perfect {X : Type*} [Group X] {G₀ J : Subgroup X} (hJG : J ≤ G₀)
    (hJ : commutator ↥J = ⊤) {b : X} {n : ↥G₀}
    (hact : ∀ y : ↥G₀, b * (y : X) * b⁻¹ = (n : X) * (y : X) * (n : X)⁻¹)
    (hcomm : ∀ j : ↥G₀, (j : X) ∈ J →
      (QuotientGroup.mk n : ↥G₀ ⧸ Subgroup.center ↥G₀) * QuotientGroup.mk j =
        QuotientGroup.mk j * QuotientGroup.mk n) :
    ∀ j ∈ J, b * j = j * b := by
  have hJ' : commutator ↥(J.subgroupOf G₀) = ⊤ := by
    have hP : Group.IsPerfect ↥J := Group.isPerfect_def.mpr hJ
    exact Group.isPerfect_def.mp (Group.IsPerfect.ofSurjective
      (f := (Subgroup.subgroupOfEquivOfLe hJG).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hJG).symm.surjective)
  have hn' : ∀ j ∈ J.subgroupOf G₀, n * j * n⁻¹ * j⁻¹ ∈ Subgroup.center ↥G₀ := by
    intro j hj
    have hjJ : (j : X) ∈ J := Subgroup.mem_subgroupOf.mp hj
    have hd : (j * n)⁻¹ * (n * j) ∈ Subgroup.center ↥G₀ := by
      have h : (QuotientGroup.mk (j * n) : ↥G₀ ⧸ Subgroup.center ↥G₀)
          = QuotientGroup.mk (n * j) := by
        rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul]
        exact (hcomm j hjJ).symm
      exact QuotientGroup.eq.mp h
    have hcd : n * j * n⁻¹ * j⁻¹ = (j * n)⁻¹ * (n * j) := by
      have hc : (n * j) * ((j * n)⁻¹ * (n * j)) = ((j * n)⁻¹ * (n * j)) * (n * j) :=
        Subgroup.mem_center_iff.mp hd (n * j)
      calc n * j * n⁻¹ * j⁻¹ = (n * j) * ((j * n)⁻¹ * (n * j)) * (n * j)⁻¹ := by group
        _ = ((j * n)⁻¹ * (n * j)) * (n * j) * (n * j)⁻¹ := by rw [hc]
        _ = (j * n)⁻¹ * (n * j) := by group
    rw [hcd]
    exact hd
  have hG := commute_of_perfect_central_commutators hJ' hn'
  intro j hj
  have hj0 : (⟨j, hJG hj⟩ : ↥G₀) ∈ J.subgroupOf G₀ := Subgroup.mem_subgroupOf.mpr hj
  have hnj : (n : X) * j = j * (n : X) := congrArg Subtype.val (hG _ hj0)
  have h2 : b * j * b⁻¹ = j := by
    calc b * j * b⁻¹ = (n : X) * j * (n : X)⁻¹ := hact ⟨j, hJG hj⟩
      _ = (j * (n : X)) * (n : X)⁻¹ := by rw [hnj]
      _ = j := by group
  exact mul_inv_eq_iff_eq_mul.mp h2

end CFSG.StandardType.TableCRes
