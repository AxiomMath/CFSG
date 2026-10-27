module

public import CFSG.Quasithin.Background.E2TwoProofTwo

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique B6

namespace E2P

section Inj

variable {G G' : Type} [Group G] [Group G'] {f : G →* G'}

theorem mem_normalizer_map_iff (hf : Function.Injective f) {P : Subgroup G} {g : G} :
    f g ∈ Subgroup.normalizer (P.map f : Set G') ↔ g ∈ Subgroup.normalizer (P : Set G) := by
  simp only [Subgroup.mem_normalizer_iff]
  constructor
  · intro h x
    have := h (f x)
    rw [← map_mul, ← map_inv, ← map_mul, Subgroup.mem_map_iff_mem hf,
      Subgroup.mem_map_iff_mem hf] at this
    exact this
  · intro h y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨g * x * g⁻¹, (h x).mp hx, by simp⟩
    · rintro ⟨z, hz, hzy⟩
      have hy : y = f (g⁻¹ * z * g) := by
        rw [map_mul, map_mul, map_inv, hzy]
        group
      rw [hy]
      refine ⟨g⁻¹ * z * g, (h _).mpr ?_, rfl⟩
      simpa [mul_assoc] using hz

theorem mem_centralizer_map_iff (hf : Function.Injective f) {P : Subgroup G} {g : G} :
    f g ∈ Subgroup.centralizer (P.map f : Set G') ↔ g ∈ Subgroup.centralizer (P : Set G) := by
  simp only [Subgroup.mem_centralizer_iff]
  constructor
  · intro h x hx
    exact hf (by rw [map_mul, map_mul]; exact h (f x) ⟨x, hx, rfl⟩)
  · rintro h _ ⟨x, hx, rfl⟩
    rw [← map_mul, ← map_mul, h x hx]

theorem zOf_map (hf : Function.Injective f) (P : Subgroup G) : (zOf P).map f = zOf (P.map f) := by
  apply le_antisymm
  · rintro _ ⟨x, ⟨hx, hxc⟩, rfl⟩
    exact ⟨⟨x, hx, rfl⟩, (mem_centralizer_map_iff hf).mpr hxc⟩
  · rintro _ ⟨⟨x, hx, rfl⟩, hxc⟩
    exact ⟨x, ⟨hx, (mem_centralizer_map_iff hf).mp hxc⟩, rfl⟩

end Inj

section AutT

variable {Y : Type} [Group Y] [Finite Y] {T M L : Subgroup Y}

@[expose] noncomputable def innIota (L : Subgroup Y) : ↥L →* ↥(autOn ⊤ L) :=
  (innAut L).codRestrict _ fun x => range_innAut_le L ⟨x, rfl⟩

omit [Finite Y] in
theorem coe_innIota (x : ↥L) : (innIota L x : MulAut ↥L) = innAut L x := rfl

omit [Finite Y] in
theorem range_innIota (L : Subgroup Y) :
    (innIota L).range = (innAut L).range.subgroupOf (autOn ⊤ L) := by
  ext φ
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x, rfl⟩
  · rintro ⟨x, hx⟩
    exact ⟨x, Subtype.ext hx⟩

omit [Finite Y] in
theorem autCard_eq_card (T L : Subgroup Y) : E2.autCard T L = Nat.card (autOn T L) := by
  unfold E2.autCard
  set N := Subgroup.normalizer (L : Set Y)
  have hker : (conjAct L).ker = (Subgroup.centralizer (L : Set Y)).subgroupOf N := by
    ext n
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, ← indAut_eq_one_iff n.2, indAut_of_mem n.2]
  have h1 := Subgroup.relIndex_ker (K := T.subgroupOf N) (conjAct L)
  rw [hker] at h1
  have h2 : ((T ⊓ N) ⊓ Subgroup.centralizer (L : Set Y)).relIndex (T ⊓ N) =
      ((Subgroup.centralizer (L : Set Y)).subgroupOf N).relIndex (T.subgroupOf N) := by
    rw [← Subgroup.relIndex_subgroupOf (inf_le_right : T ⊓ N ≤ N)]
    have e1 : ((T ⊓ N) ⊓ Subgroup.centralizer (L : Set Y)).subgroupOf N =
        (Subgroup.centralizer (L : Set Y)).subgroupOf N ⊓ T.subgroupOf N := by
      ext x
      simp [Subgroup.mem_subgroupOf, and_comm]
    have e2 : (T ⊓ N).subgroupOf N = T.subgroupOf N := by
      ext x
      simp [Subgroup.mem_subgroupOf]
    rw [e1, e2]
    exact Subgroup.inf_relIndex_right _ _
  rw [h2, h1]
  rfl

namespace Factor

variable (hF : Factor T M L)
include hF

omit [Finite Y] in
theorem innIota_injective : Function.Injective (innIota L) := fun _ _ h =>
  innAut_injective hF.simple hF.nonab (congrArg Subtype.val h)

noncomputable def innEquiv : ↥L ≃* ↥((innAut L).range.subgroupOf (autOn ⊤ L)) :=
  (MonoidHom.ofInjective hF.innIota_injective).trans (MulEquiv.subgroupCongr (range_innIota L))

theorem innIota_mem_T_iff (x : ↥L) :
    innIota L x ∈ (autOn T L).subgroupOf (autOn ⊤ L) ↔ (x : Y) ∈ T := by
  obtain ⟨C, d⟩ := hF.exists_autData
  rw [Subgroup.mem_subgroupOf, coe_innIota]
  constructor
  · intro hx
    have hSyl : IsSylowTwoOf ((T ⊓ L).subgroupOf L) (⊤ : Subgroup ↥L) := by
      refine ⟨le_top, d.sylow_TL.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe inf_le_right).symm, ?_⟩
      have h := d.sylow_TL.2.2
      have e : (((T ⊓ L).subgroupOf L).subgroupOf ⊤).index = ((T ⊓ L).subgroupOf L).index :=
        Subgroup.relIndex_top_right _
      rw [e]
      exact h
    have hle : (T ⊓ L).subgroupOf L ≤ innPre T L := by
      intro y hy
      rw [mem_innPre, ← indAut_eq_innAut]
      exact indAut_mem_autOn (Subgroup.mem_subgroupOf.mp hy).1 (Subgroup.le_normalizer y.2)
    have heq := eq_of_isSylowTwoOf_le hSyl d.isPGroup_innPre hle le_top
    have : x ∈ innPre T L := hx
    rw [heq] at this
    exact (Subgroup.mem_subgroupOf.mp this).1
  · intro hx
    rw [← indAut_eq_innAut]
    exact indAut_mem_autOn hx (Subgroup.le_normalizer x.2)

theorem map_innIota_T :
    ((T ⊓ L).subgroupOf L).map (innIota L) =
      (autOn T L).subgroupOf (autOn ⊤ L) ⊓ (innAut L).range.subgroupOf (autOn ⊤ L) := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact ⟨(hF.innIota_mem_T_iff x).mpr (Subgroup.mem_subgroupOf.mp hx).1, ⟨x, rfl⟩⟩
  · rintro φ ⟨hφT, hφK⟩
    rw [← range_innIota] at hφK
    obtain ⟨x, rfl⟩ := hφK
    exact ⟨x, Subgroup.mem_subgroupOf.mpr ⟨(hF.innIota_mem_T_iff x).mp hφT, x.2⟩, rfl⟩

theorem autCard_eq :
    E2.autCard ((autOn T L).subgroupOf (autOn ⊤ L)) ((innAut L).range.subgroupOf (autOn ⊤ L)) =
      E2.autCard T L := by
  have hX := hF.asHyp_autOn
  rw [autCard_eq_card T L]
  unfold E2.autCard
  have hN : Subgroup.normalizer
      (((innAut L).range.subgroupOf (autOn ⊤ L) : Subgroup ↥(autOn ⊤ L)) : Set ↥(autOn ⊤ L)) = ⊤ :=
    Subgroup.normalizer_eq_top_iff.mpr hX.normal
  rw [hN, hX.cent, inf_top_eq, inf_bot_eq, Subgroup.relIndex_bot_left]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (autOn_le_autOn_of_le le_top)).toEquiv

end Factor

namespace TwoConj

variable {t : Y} (h2 : TwoConj T L t) (hF : Factor T M L)
include h2 hF

theorem innIota_mem_M_iff (x : ↥L) :
    innIota L x ∈ (autOn M L).subgroupOf (autOn ⊤ L) ↔ (x : Y) ∈ M := by
  rw [Subgroup.mem_subgroupOf, coe_innIota]
  have heq := h2.inf_M_eq hF
  constructor
  · intro hx
    have : (x : Y) ∈ xOne M L :=
      ⟨⟨Subgroup.le_normalizer x.2, by rw [indAut_eq_innAut]; exact hx⟩, x.2⟩
    rw [← heq] at this
    exact this.1
  · intro hx
    have : (x : Y) ∈ xOne M L := by rw [← heq]; exact ⟨hx, x.2⟩
    rw [← indAut_eq_innAut]
    exact this.1.2

theorem isBorelIn_of_aut
    (h : E2.IsBorelIn ((innAut L).range.subgroupOf (autOn ⊤ L))
      ((autOn M L).subgroupOf (autOn ⊤ L) ⊓ (innAut L).range.subgroupOf (autOn ⊤ L))) :
    E2.IsBorelIn L (M ⊓ L) := by
  obtain ⟨S', hS', hB⟩ := h
  have hinj := hF.innIota_injective
  set S₀ := S'.comap (innIota L)
  have hS'K : S' ≤ (innIota L).range := by rw [range_innIota]; exact hS'.1
  have hS'map : S₀.map (innIota L) = S' := Subgroup.map_comap_eq_self hS'K
  refine ⟨S₀.map L.subtype, ⟨?_, ?_, ?_⟩, ?_⟩
  · rintro _ ⟨x, -, rfl⟩
    exact x.2
  · have h1 : IsPGroup 2 S₀ := hS'.2.1.comap_of_injective _ hinj
    exact h1.map _
  · have : (S₀.map L.subtype).subgroupOf L = S₀ :=
      Subgroup.comap_map_eq_self_of_injective L.subtype_injective S₀
    rw [this, Subgroup.index_comap, range_innIota]
    exact hS'.2.2
  · ext y
    constructor
    · rintro ⟨hyM, hyL⟩
      refine ⟨hyL, ?_⟩
      have hy := (h2.innIota_mem_M_iff hF ⟨y, hyL⟩).mpr hyM
      have hyK : innIota L ⟨y, hyL⟩ ∈ (innAut L).range.subgroupOf (autOn ⊤ L) := by
        rw [← range_innIota]
        exact ⟨_, rfl⟩
      have hyB : innIota L ⟨y, hyL⟩ ∈ (autOn M L).subgroupOf (autOn ⊤ L) ⊓
          (innAut L).range.subgroupOf (autOn ⊤ L) := ⟨hy, hyK⟩
      rw [hB] at hyB
      have h1 := hyB.2
      rw [← hS'map] at h1
      have h3 := (mem_normalizer_map_iff hinj).mp h1
      have h4 := (mem_normalizer_map_iff L.subtype_injective (g := ⟨y, hyL⟩)).mpr h3
      exact h4
    · rintro ⟨hyL, hyN⟩
      refine ⟨?_, hyL⟩
      have h3 := (mem_normalizer_map_iff L.subtype_injective (g := ⟨y, hyL⟩)).mp hyN
      have h1 := (mem_normalizer_map_iff hinj).mpr h3
      rw [hS'map] at h1
      have hyK : innIota L ⟨y, hyL⟩ ∈ (innAut L).range.subgroupOf (autOn ⊤ L) := by
        rw [← range_innIota]
        exact ⟨_, rfl⟩
      have hyB : innIota L ⟨y, hyL⟩ ∈ (innAut L).range.subgroupOf (autOn ⊤ L) ⊓
          Subgroup.normalizer (S' : Set ↥(autOn ⊤ L)) := ⟨hyK, h1⟩
      rw [← hB] at hyB
      exact (h2.innIota_mem_M_iff hF ⟨y, hyL⟩).mp hyB.1

theorem inf_eq_centralizer_of_aut
    (h : (autOn M L).subgroupOf (autOn ⊤ L) ⊓ (innAut L).range.subgroupOf (autOn ⊤ L) =
      (innAut L).range.subgroupOf (autOn ⊤ L) ⊓ Subgroup.centralizer
        (zOf ((autOn T L).subgroupOf (autOn ⊤ L) ⊓ (innAut L).range.subgroupOf (autOn ⊤ L)) :
          Set ↥(autOn ⊤ L))) :
    M ⊓ L = L ⊓ Subgroup.centralizer (zOf (T ⊓ L) : Set Y) := by
  have hinj := hF.innIota_injective
  rw [← hF.map_innIota_T, ← zOf_map hinj] at h
  have hZ : (zOf ((T ⊓ L).subgroupOf L)).map L.subtype = zOf (T ⊓ L) := by
    rw [zOf_map L.subtype_injective, Subgroup.map_subgroupOf_eq_of_le inf_le_right]
  have hyK : ∀ y (hyL : y ∈ L), innIota L ⟨y, hyL⟩ ∈ (innAut L).range.subgroupOf (autOn ⊤ L) :=
    fun y hyL => by rw [← range_innIota]; exact ⟨_, rfl⟩
  ext y
  constructor
  · rintro ⟨hyM, hyL⟩
    refine ⟨hyL, ?_⟩
    have hyB : innIota L ⟨y, hyL⟩ ∈ (autOn M L).subgroupOf (autOn ⊤ L) ⊓
        (innAut L).range.subgroupOf (autOn ⊤ L) :=
      ⟨(h2.innIota_mem_M_iff hF ⟨y, hyL⟩).mpr hyM, hyK y hyL⟩
    rw [h] at hyB
    have h3 := (mem_centralizer_map_iff hinj).mp hyB.2
    rw [← hZ]
    exact (mem_centralizer_map_iff L.subtype_injective (g := ⟨y, hyL⟩)).mpr h3
  · rintro ⟨hyL, hyC⟩
    refine ⟨?_, hyL⟩
    rw [← hZ] at hyC
    have h3 := (mem_centralizer_map_iff L.subtype_injective (g := ⟨y, hyL⟩)).mp hyC
    have hyB : innIota L ⟨y, hyL⟩ ∈ (innAut L).range.subgroupOf (autOn ⊤ L) ⊓
        Subgroup.centralizer ((zOf ((T ⊓ L).subgroupOf L)).map (innIota L) :
          Set ↥(autOn ⊤ L)) := ⟨hyK y hyL, (mem_centralizer_map_iff hinj).mpr h3⟩
    rw [← h] at hyB
    exact (h2.innIota_mem_M_iff hF ⟨y, hyL⟩).mp hyB.1

end TwoConj

end AutT

end E2P

end CFSG.Quasithin
