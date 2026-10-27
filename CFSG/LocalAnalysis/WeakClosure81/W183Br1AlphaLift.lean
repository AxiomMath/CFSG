module

public import CFSG.LocalAnalysis.WeakClosure81.W183Abs4
public import CFSG.LocalAnalysis.WeakClosure81.EightEightDefs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup

private theorem w183_map_conj {X X' : Type*} [Group X] [Group X'] (π : X →* X')
    (A : Subgroup X) (g : X) :
    (A.map (MulAut.conj g).toMonoidHom).map π =
      (A.map π).map (MulAut.conj (π g)).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, map_mul, map_inv]

private theorem w183_map_le_map_iff {G G' : Type*} [Group G] [Group G'] {ψ : G →* G'}
    {L : Subgroup G} (hinj : ∀ a ∈ L, ∀ b ∈ L, ψ a = ψ b → a = b) {A B : Subgroup G}
    (hA : A ≤ L) (hB : B ≤ L) : A.map ψ ≤ B.map ψ ↔ A ≤ B := by
  constructor
  · intro h a ha
    obtain ⟨b, hb, hbψ⟩ := Subgroup.mem_map.mp (h (Subgroup.mem_map.mpr ⟨a, ha, rfl⟩))
    have hab : a = b := hinj a (hA ha) b (hB hb) hbψ.symm
    simpa [hab] using hb
  · exact Subgroup.map_mono

private theorem w183_map_eq_map_iff {G G' : Type*} [Group G] [Group G'] {ψ : G →* G'}
    {L : Subgroup G} (hinj : ∀ a ∈ L, ∀ b ∈ L, ψ a = ψ b → a = b) {A B : Subgroup G}
    (hA : A ≤ L) (hB : B ≤ L) : A.map ψ = B.map ψ ↔ A = B := by
  constructor
  · intro h
    exact le_antisymm ((w183_map_le_map_iff hinj hA hB).mp h.le)
      ((w183_map_le_map_iff hinj hB hA).mp h.ge)
  · intro h
    rw [h]

private theorem w183_map_lt_map_iff {G G' : Type*} [Group G] [Group G'] {ψ : G →* G'}
    {L : Subgroup G} (hinj : ∀ a ∈ L, ∀ b ∈ L, ψ a = ψ b → a = b) {A B : Subgroup G}
    (hA : A ≤ L) (hB : B ≤ L) : A.map ψ < B.map ψ ↔ A < B := by
  constructor
  · intro h
    exact lt_of_le_of_ne ((w183_map_le_map_iff hinj hA hB).mp h.le)
      (fun hab => h.not_ge (by rw [← hab]))
  · intro h
    exact lt_of_le_of_ne (Subgroup.map_mono h.le)
      (fun hmap => h.not_ge ((w183_map_le_map_iff hinj hB hA).mp hmap.ge))

private theorem w183_relIndex_map_map {G G' : Type*} [Group G] [Group G'] {ψ : G →* G'}
    {L : Subgroup G} (hinj : ∀ a ∈ L, ∀ b ∈ L, ψ a = ψ b → a = b) {S : Subgroup G}
    (hS : S ≤ L) : (S.map ψ).relIndex (L.map ψ) = S.relIndex L := by
  let φ : ↥L →* G' := ψ.comp L.subtype
  have hφ : Function.Injective φ := by
    intro a b h
    exact Subtype.ext (hinj a.1 a.2 b.1 b.2 h)
  have hS' : (S.subgroupOf L).map φ = S.map ψ := by
    ext x
    constructor
    · intro hx
      obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp hx
      exact Subgroup.mem_map.mpr ⟨s, Subgroup.mem_subgroupOf.mp hs, rfl⟩
    · intro hx
      obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp hx
      exact Subgroup.mem_map.mpr ⟨⟨s, hS hs⟩, Subgroup.mem_subgroupOf.mpr hs, rfl⟩
  have htop : (⊤ : Subgroup ↥L).map φ = L.map ψ := by
    ext x
    constructor
    · intro hx
      obtain ⟨l, -, rfl⟩ := Subgroup.mem_map.mp hx
      exact Subgroup.mem_map.mpr ⟨l, l.2, rfl⟩
    · intro hx
      obtain ⟨l, hl, rfl⟩ := Subgroup.mem_map.mp hx
      exact Subgroup.mem_map.mpr ⟨⟨l, hl⟩, Subgroup.mem_top _, rfl⟩
  rw [← hS', ← htop,
    Subgroup.relIndex_map_map_of_injective (f := φ) (S.subgroupOf L) ⊤ hφ,
    Subgroup.relIndex_top_right]
  rfl

private theorem w183_mem_normalizer_map_iff {G G' : Type*} [Group G] [Group G'] {ψ : G →* G'}
    {L : Subgroup G} (hinj : ∀ a ∈ L, ∀ b ∈ L, ψ a = ψ b → a = b) {B : Subgroup G}
    (hB : B ≤ L) {x : G} (hx : x ∈ L) :
    ψ x ∈ Subgroup.normalizer ((B.map ψ : Subgroup G') : Set G') ↔
      x ∈ Subgroup.normalizer (B : Set G) := by
  rw [Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
  constructor
  · intro h b
    constructor
    · intro hb
      have hmem : ψ (x * b * x⁻¹) ∈ B.map ψ := by
        rw [map_mul, map_mul, map_inv]
        exact (h (ψ b)).mp (Subgroup.mem_map.mpr ⟨b, hb, rfl⟩)
      obtain ⟨b', hb', hb'π⟩ := Subgroup.mem_map.mp hmem
      have hbb' : x * b * x⁻¹ = b' :=
        hinj (x * b * x⁻¹) (L.mul_mem (L.mul_mem hx (hB hb)) (L.inv_mem hx)) b' (hB hb')
          hb'π.symm
      simpa [hbb'] using hb'
    · intro hb
      have hbL : b ∈ L := by
        have hb_eq : b = x⁻¹ * (x * b * x⁻¹) * x := by group
        rw [hb_eq]
        exact L.mul_mem (L.mul_mem (L.inv_mem hx) (hB hb)) hx
      have hmem : ψ b ∈ B.map ψ :=
        (h (ψ b)).mpr (Subgroup.mem_map.mpr ⟨x * b * x⁻¹, hb, by
          rw [map_mul, map_mul, map_inv]⟩)
      obtain ⟨b', hb', hb'π⟩ := Subgroup.mem_map.mp hmem
      have hbb' : b = b' := hinj b hbL b' (hB hb') hb'π.symm
      simpa [hbb'] using hb'
  · intro hx y
    constructor
    · intro hy
      obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hy
      exact Subgroup.mem_map.mpr
        ⟨x * b * x⁻¹, (Subgroup.mem_normalizer_iff.mp hx b).mp hb,
          by rw [map_mul, map_mul, map_inv]⟩
    · intro hy
      obtain ⟨b, hb, hbπ⟩ := Subgroup.mem_map.mp hy
      have hb' : x⁻¹ * b * x ∈ B :=
        (Subgroup.mem_normalizer_iff.mp hx (x⁻¹ * b * x)).mpr (by simpa [mul_assoc] using hb)
      refine Subgroup.mem_map.mpr ⟨x⁻¹ * b * x, hb', ?_⟩
      rw [map_mul, map_mul, map_inv, hbπ]
      group

private theorem w183_map_comap_inf {G G' : Type*} [Group G] [Group G'] (ψ : G →* G')
    {L : Subgroup G} {Y' : Subgroup G'} (hY' : Y' ≤ L.map ψ) :
    ((Y'.comap ψ) ⊓ L).map ψ = Y' := by
  apply le_antisymm
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
    exact (Subgroup.mem_inf.mp hx).1
  · intro y hy
    obtain ⟨l, hl, rfl⟩ := Subgroup.mem_map.mp (hY' hy)
    exact Subgroup.mem_map.mpr ⟨l, Subgroup.mem_inf.mpr
      ⟨Subgroup.mem_comap.mpr (by simpa using hy), hl⟩, rfl⟩

private theorem w183_conjSubgroup_map {G G' : Type*} [Group G] [Group G'] (ψ : G →* G')
    (A : Subgroup G) (g : G) :
    conjSubgroup (A.map ψ) (ψ g) = (conjSubgroup A g).map ψ := by
  unfold conjSubgroup
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, map_mul, map_inv]

private theorem w183_conjSubgroup_le_of_mem_normalizer {G : Type*} [Group G]
    {P L : Subgroup G} (hP : P ≤ L) {g : G}
    (hg : g ∈ Subgroup.normalizer (L : Set G)) : conjSubgroup P g ≤ L := by
  intro x hx
  rw [conjSubgroup, Subgroup.mem_map] at hx
  obtain ⟨p, hp, rfl⟩ := hx
  have h := (Subgroup.mem_normalizer_iff''.mp hg p).mp (hP hp)
  simpa [MulAut.conj_apply] using h

theorem w183_corConfig_lift {X X' : Type*} [Group X] [Group X'] (π : X →* X')
    (hπ : Function.Surjective π) {G₂ : Subgroup X} (hG₂ : G₂.Normal)
    (hinj : ∀ a ∈ G₂, ∀ b ∈ G₂, π a = π b → a = b) {A₀ : Subgroup X} (hA₀ : A₀ ≤ G₂)
    (h : CorConfig X' (A₀.map π)) : CorConfig X A₀ := by
  obtain ⟨A', S, y, hA', hS, hy, hrel, hnn, hcomm⟩ := h
  obtain ⟨gbar, hA'eq⟩ := hA'
  obtain ⟨g₀, hg₀⟩ := hπ gbar
  obtain ⟨ŷ, hŷ⟩ := hπ y
  let Ŝ : Set (Subgroup X) :=
    {Z : Subgroup X | ∃ g : X, Z = A₀.map (MulAut.conj g).toMonoidHom ∧ Z.map π ∈ S}
  have hconj_le : ∀ g : X, A₀.map (MulAut.conj g).toMonoidHom ≤ G₂ := by
    intro g x hx
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
    exact hG₂.conj_mem a (hA₀ ha) g
  have hmem_eq : ∀ {A B : Subgroup X}, A ≤ G₂ → B ≤ G₂ → A.map π = B.map π → A = B := by
    intro A B hA hB hAB
    apply le_antisymm
    · intro a ha
      have ha' : π a ∈ B.map π := by
        rw [← hAB]
        exact Subgroup.mem_map.mpr ⟨a, ha, rfl⟩
      obtain ⟨b, hb, hbπ⟩ := Subgroup.mem_map.mp ha'
      have hab : a = b := hinj a (hA ha) b (hB hb) hbπ.symm
      simpa [hab] using hb
    · intro b hb
      have hb' : π b ∈ A.map π := by
        rw [hAB]
        exact Subgroup.mem_map.mpr ⟨b, hb, rfl⟩
      obtain ⟨a, ha, haπ⟩ := Subgroup.mem_map.mp hb'
      have hab : a = b := hinj a (hA ha) b (hB hb) haπ
      simpa [hab] using ha
  have hA'map : (A₀.map (MulAut.conj g₀).toMonoidHom).map π = A' := by
    rw [w183_map_conj π A₀ g₀, hg₀, ← hA'eq]
  refine ⟨A₀.map (MulAut.conj g₀).toMonoidHom, Ŝ, ŷ, ⟨g₀, rfl⟩, ?_, ?_, ?_, ?_, ?_⟩
  · intro Z hZ
    obtain ⟨g, rfl, -⟩ := hZ
    exact ⟨g, rfl⟩
  · intro hconj
    apply hy
    have hcongr := congrArg (Subgroup.map π) hconj
    rwa [w183_map_conj π A₀ ŷ, hŷ] at hcongr
  · intro s hs
    have hsπ : π s ∈ A₀.map π := Subgroup.mem_map.mpr ⟨s, hs, rfl⟩
    obtain ⟨zt, hzt, hztrel⟩ := hrel (π s) hsπ
    have hT : (⋃ X ∈ S, (X : Set X')) = π '' (⋃ Z ∈ Ŝ, (Z : Set X)) := by
      ext x
      constructor
      · intro hx
        rcases Set.mem_iUnion.mp hx with ⟨X, hx⟩
        rcases Set.mem_iUnion.mp hx with ⟨hXS, hxX⟩
        obtain ⟨gbar, hgbar⟩ := hS X hXS
        obtain ⟨g, hg⟩ := hπ gbar
        have hX : X = (A₀.map (MulAut.conj g).toMonoidHom).map π := by
          rw [hgbar, ← hg, ← w183_map_conj π A₀ g]
        have hZS : (A₀.map (MulAut.conj g).toMonoidHom).map π ∈ S := by
          rw [← hX]
          exact hXS
        rw [hX] at hxX
        obtain ⟨z, hz, hzπ⟩ := Subgroup.mem_map.mp hxX
        exact ⟨z, Set.mem_iUnion.mpr ⟨A₀.map (MulAut.conj g).toMonoidHom,
          Set.mem_iUnion.mpr ⟨⟨g, rfl, hZS⟩, hz⟩⟩, hzπ⟩
      · rintro ⟨z, hz, rfl⟩
        rcases Set.mem_iUnion.mp hz with ⟨Z, hz⟩
        rcases Set.mem_iUnion.mp hz with ⟨hZ, hzZ⟩
        obtain ⟨g, rfl, hgS⟩ := hZ
        exact Set.mem_iUnion.mpr ⟨(A₀.map (MulAut.conj g).toMonoidHom).map π,
          Set.mem_iUnion.mpr ⟨hgS, Subgroup.mem_map.mpr ⟨z, hzZ, rfl⟩⟩⟩
    have hclosure : Subgroup.closure (⋃ X ∈ S, (X : Set X')) =
        (Subgroup.closure (⋃ Z ∈ Ŝ, (Z : Set X))).map π := by
      rw [MonoidHom.map_closure, hT]
    have hzt' : zt ∈ (Subgroup.closure (⋃ Z ∈ Ŝ, (Z : Set X))).map π := by
      rw [← hclosure]
      exact hzt
    obtain ⟨z, hz, hzπ⟩ := Subgroup.mem_map.mp hzt'
    have hsub : (⋃ Z ∈ Ŝ, (Z : Set X)) ⊆ G₂ := by
      intro x hx
      rcases Set.mem_iUnion.mp hx with ⟨Z, hx⟩
      rcases Set.mem_iUnion.mp hx with ⟨hZ, hxZ⟩
      obtain ⟨g, rfl, -⟩ := hZ
      exact hconj_le g hxZ
    have hclosure_le : Subgroup.closure (⋃ Z ∈ Ŝ, (Z : Set X)) ≤ G₂ :=
      (Subgroup.closure_le G₂).mpr hsub
    refine ⟨z, hz, ?_⟩
    exact hinj (ŷ * s * ŷ⁻¹) (hG₂.conj_mem s (hA₀ hs) ŷ)
      (s * z) (G₂.mul_mem (hA₀ hs) (hclosure_le hz))
      (by simpa [map_mul, map_inv, hŷ, hzπ] using hztrel)
  · intro hnorm
    have hmapnorm : A₀.map π ≤ Subgroup.normalizer (A' : Set X') := by
      have h1 : A₀.map π ≤ (Subgroup.normalizer
          ((A₀.map (MulAut.conj g₀).toMonoidHom) : Set X)).map π := Subgroup.map_mono hnorm
      have h2 : (Subgroup.normalizer
          ((A₀.map (MulAut.conj g₀).toMonoidHom) : Set X)).map π ≤
            Subgroup.normalizer (A' : Set X') := by
        have hle := Subgroup.le_normalizer_map
          (H := A₀.map (MulAut.conj g₀).toMonoidHom) π
        rwa [hA'map] at hle
      exact h1.trans h2
    exact hnn hmapnorm
  · intro Z hZ
    obtain ⟨g, rfl, hgS⟩ := hZ
    have hZle : A₀.map (MulAut.conj g).toMonoidHom ≤ G₂ := hconj_le g
    rcases hcomm ((A₀.map (MulAut.conj g).toMonoidHom).map π) hgS with hEq | hComm
    · left
      exact hmem_eq hZle (hconj_le g₀) (by rw [hEq, hA'map])
    · right
      intro a ha x hx
      have ha' : π a ∈ A' := by
        rw [← hA'map]
        exact Subgroup.mem_map.mpr ⟨a, ha, rfl⟩
      have hx' : π x ∈ (A₀.map (MulAut.conj g).toMonoidHom).map π :=
        Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
      exact hinj (a * x) (G₂.mul_mem (hconj_le g₀ ha) (hZle hx))
        (x * a) (G₂.mul_mem (hZle hx) (hconj_le g₀ ha)) (by
          rw [map_mul, map_mul]
          exact hComm (π a) ha' (π x) hx')

variable {G G' : Type} [Group G] [Group G'] [Finite G] [Finite G']

theorem w183_actsOnDynkin_map (ψ : G →* G') {L : Subgroup G}
    (hinj : ∀ a ∈ L, ∀ b ∈ L, ψ a = ψ b → a = b) {t : G} (h : ActsOnDynkinMod ⊥ L t) :
    ActsOnDynkinMod ⊥ (L.map ψ) (ψ t) := by
  obtain ⟨htN, P, hPmax, hmove⟩ := h
  obtain ⟨_, hPltL, hmax, S, _, hSL, hSpow, hSodd, hSnorm⟩ := hPmax
  have hP : P ≤ L := hPltL.1
  have htN' : ψ t ∈ (Subgroup.normalizer (L : Set G)).map ψ :=
    Subgroup.mem_map.mpr ⟨t, htN, rfl⟩
  refine ⟨(Subgroup.le_normalizer_map ψ) htN', P.map ψ, ?_, ?_⟩
  · refine ⟨bot_le, (w183_map_lt_map_iff hinj hP le_rfl).mpr hPltL, ?_,
      S.map ψ, bot_le, Subgroup.map_mono hSL, ?_, ?_, ?_⟩
    · intro Y' hPY' hY'L
      have hle : P ≤ (Y'.comap ψ) ⊓ L := by
        intro p hp
        exact Subgroup.mem_inf.mpr
          ⟨Subgroup.mem_comap.mpr (hPY'.1 (Subgroup.mem_map.mpr ⟨p, hp, rfl⟩)), hP hp⟩
      have hPY₀ : P < (Y'.comap ψ) ⊓ L := by
        refine lt_of_le_of_ne hle ?_
        intro heq
        exact hPY'.not_ge (by rw [heq, w183_map_comap_inf ψ hY'L])
      have hY₀ : (Y'.comap ψ) ⊓ L = L :=
        hmax ((Y'.comap ψ) ⊓ L) hPY₀ inf_le_right
      calc Y' = ((Y'.comap ψ) ⊓ L).map ψ := (w183_map_comap_inf ψ hY'L).symm
        _ = L.map ψ := by rw [hY₀]
    · intro s' hs'
      obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp hs'
      obtain ⟨k, hk⟩ := hSpow s hs
      refine ⟨k, ?_⟩
      rw [← map_pow, Subgroup.mem_bot.mp hk, map_one]
      exact Subgroup.mem_bot.mpr rfl
    · rw [w183_relIndex_map_map hinj hSL]
      exact hSodd
    · intro x hx
      rw [Subgroup.mem_inf] at hx
      obtain ⟨hxL, hxN⟩ := hx
      obtain ⟨l, hl, rfl⟩ := Subgroup.mem_map.mp hxL
      exact Subgroup.mem_map.mpr ⟨l, hSnorm (Subgroup.mem_inf.mpr
        ⟨hl, (w183_mem_normalizer_map_iff hinj hSL hl).mp hxN⟩), rfl⟩
  · intro l' hl'
    obtain ⟨l, hl, rfl⟩ := Subgroup.mem_map.mp hl'
    intro heq
    have hg : t⁻¹ * l ∈ Subgroup.normalizer (L : Set G) :=
      (Subgroup.normalizer (L : Set G)).mul_mem
        ((Subgroup.normalizer (L : Set G)).inv_mem htN)
        (Subgroup.le_normalizer (H := L) hl)
    have hconj : (conjSubgroup P (t⁻¹ * l)).map ψ = P.map ψ := by
      rw [← w183_conjSubgroup_map ψ P (t⁻¹ * l),
        show ψ (t⁻¹ * l) = (ψ t)⁻¹ * ψ l by rw [map_mul, map_inv]]
      exact heq
    exact hmove l hl ((w183_map_eq_map_iff hinj
      (w183_conjSubgroup_le_of_mem_normalizer hP hg) hP).mp hconj)

end CFSG.LocalAnalysis.WeakClosure81

end
