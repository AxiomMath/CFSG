module

public import CFSG.Timmesfeld.ARS.SimplyLacedConfigA
public import CFSG.Timmesfeld.ARS.Sec13Restrict

public section

namespace CFSG.Timmesfeld.ARS

open CFSG.Timmesfeld.RankOne CFSG.LieType CFSG.LieType.Universal Matrix CFSG.Blueprint

variable {G : Type} [Group G] {R : Set (Subgroup G)}

theorem iSup_subgroupOf_eq_top_of_iSup_eq {r : ℕ} {A B : Fin r → Subgroup G} {L : Subgroup G}
    (hgen : ⨆ k, (A k ⊔ B k) = L) : ⨆ k, ((A k).subgroupOf L ⊔ (B k).subgroupOf L) = ⊤ := by
  have hle : ∀ k, A k ⊔ B k ≤ L := fun k => hgen ▸ le_iSup (fun k => A k ⊔ B k) k
  apply Subgroup.map_injective L.subtype_injective
  rw [Subgroup.map_iSup, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hk : ∀ k, ((A k).subgroupOf L ⊔ (B k).subgroupOf L).map L.subtype = A k ⊔ B k :=
    fun k => by
      rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le (le_sup_left.trans (hle k)),
        Subgroup.map_subgroupOf_eq_of_le (le_sup_right.trans (hle k))]
  rw [iSup_congr hk]
  exact hgen

theorem map_codRestrict_eq {K : Type*} [Group K] {L : Subgroup G} (f : K →* G)
    (hf : ∀ g, f g ∈ L) {S : Subgroup K} {X : Subgroup G} (hX : X ≤ L) (hSX : S.map f = X) :
    S.map (f.codRestrict L hf) = X.subgroupOf L := by
  apply Subgroup.map_injective L.subtype_injective
  rw [Subgroup.map_map, Subgroup.map_subgroupOf_eq_of_le hX]
  exact hSX

theorem IsConfig.exists_frame_le [Finite G] (hR : IsRootClass R) (hiso : NoIsolated R) {r : ℕ}
    {adj : Fin r → Fin r → Prop} {A B : Fin r → Subgroup G} (hX : IsConfig R adj A B)
    {par : Fin r → Fin r} {dep : Fin r → ℕ} {k₀ : Fin r} (hT : IsRootedTree adj par dep k₀)
    {L : Subgroup G} (hle : ∀ k, A k ⊔ B k ≤ L) :
    ∃ n : ℕ, 1 ≤ n ∧ ∃ ρ : Fin r → SpecialLinearGroup (Fin 2) (GaloisField 2 n) →* ↥L,
      (∀ k, (upperUnipotent _).map (ρ k) = (A k).subgroupOf L ∧
        (lowerUnipotent _).map (ρ k) = (B k).subgroupOf L) ∧
      ∀ i j, adj i j → ∃ ψ : SpecialLinearGroup (Fin 3) (GaloisField 2 n) →* ↥L, ∀ c,
        ψ (tv 0 1 c) = ρ i (tv 0 1 c) ∧ ψ (tv 1 0 c) = ρ i (tv 1 0 c) ∧
        ψ (tv 1 2 c) = ρ j (tv 0 1 c) ∧ ψ (tv 2 1 c) = ρ j (tv 1 0 c) := by
  obtain ⟨n, hn, -, ρ, hρ, hedge⟩ := hX.exists_frame hR hiso hT
  set F := GaloisField 2 n
  have hρL : ∀ k g, ρ k g ∈ L := fun k g => by
    have hr : (ρ k).range = A k ⊔ B k := by
      rw [MonoidHom.range_eq_map, ← NaturalModule.upperUnipotent_sup_lowerUnipotent,
        Subgroup.map_sup, (hρ k).2.1, (hρ k).2.2]
    exact hle k (hr ▸ ⟨g, rfl⟩)
  refine ⟨n, hn, fun k => (ρ k).codRestrict L (hρL k), fun k =>
    ⟨map_codRestrict_eq _ _ (le_sup_left.trans (hle k)) (hρ k).2.1,
      map_codRestrict_eq _ _ (le_sup_right.trans (hle k)) (hρ k).2.2⟩, fun i j hij => ?_⟩
  obtain ⟨ψ, hψ⟩ := hedge i j hij
  have hψL : ∀ g, ψ g ∈ L := by
    have hfund : ∀ (k : Fin 2) (s : Bool),
        SpecialLinear.fundamentalRootSubgroup 2 F k s ≤ L.comap ψ := by
      intro k s x hx
      cases s
      · change x ∈ SpecialLinear.rootSubgroup 2 F _ at hx
        obtain ⟨c, rfl⟩ := (SpecialLinear.mem_rootSubgroup _ x).1 hx
        rw [Subgroup.mem_comap, ← tv_of_ne]
        fin_cases k
        · exact (hψ c).2.1 ▸ hρL i _
        · exact (hψ c).2.2.2 ▸ hρL j _
      · change x ∈ SpecialLinear.rootSubgroup 2 F _ at hx
        obtain ⟨c, rfl⟩ := (SpecialLinear.mem_rootSubgroup _ x).1 hx
        rw [Subgroup.mem_comap, ← tv_of_ne]
        fin_cases k
        · exact (hψ c).1 ▸ hρL i _
        · exact (hψ c).2.2.1 ▸ hρL j _
    intro g
    have htop : (⊤ : Subgroup (SpecialLinearGroup (Fin (2 + 1)) F)) ≤ L.comap ψ := by
      rw [← SpecialLinear.iSup_fundamentalRootSubgroup_eq_top]
      exact iSup_le fun k => iSup_le fun s => hfund k s
    exact htop (Subgroup.mem_top g)
  refine ⟨ψ.codRestrict L hψL, fun c => ?_⟩
  obtain ⟨h1, h2, h3, h4⟩ := hψ c
  exact ⟨Subtype.ext h1, Subtype.ext h2, Subtype.ext h3, Subtype.ext h4⟩

theorem IsConfig.exists_surjective_D_le [Finite G] (hR : IsRootClass R) (hiso : NoIsolated R)
    {L : Subgroup G} {n : ℕ} (hn : 4 ≤ n) {A B : Fin n → Subgroup G}
    (hX : IsConfig R (edgeD n) A B) (hgen : ⨆ k, (A k ⊔ B k) = L) :
    ∃ f : ℕ, 1 ≤ f ∧
      ∃ Ψ : _ →* ↥L,
        (∀ k, ((Spin.plusDatum n (GaloisField 2 f) (by omega)).rootGroup (sroot k)).map Ψ =
          (A k).subgroupOf L) ∧
        (∀ k, ((Spin.plusDatum n (GaloisField 2 f) (by omega)).rootGroup (-sroot k)).map Ψ =
          (B k).subgroupOf L) ∧ Function.Surjective Ψ := by
  have hle : ∀ k, A k ⊔ B k ≤ L := fun k => hgen ▸ le_iSup (fun k => A k ⊔ B k) k
  obtain ⟨f, hf, ρ, hρ, hedge⟩ := hX.exists_frame_le hR hiso (isRootedTree_D hn) hle
  have hn3 : 3 ≤ n := by omega
  set F := GaloisField 2 f
  have hF : Nat.card F = 2 ^ f := GaloisField.card 2 f (by omega)
  have hnonadj : ∀ i j, i ≠ j → ¬ edgeD n i j → ¬ edgeD n j i →
      Commuting ((A i).subgroupOf L) ((A j).subgroupOf L) ∧
      Commuting ((A i).subgroupOf L) ((B j).subgroupOf L) ∧
      Commuting ((B i).subgroupOf L) ((A j).subgroupOf L) ∧
      Commuting ((B i).subgroupOf L) ((B j).subgroupOf L) := by
    intro i j hij h1 h2
    obtain ⟨c1, c2, c3, c4⟩ := hX.nonadj i j hij h1 h2
    have hA := fun k => le_sup_left.trans (hle k)
    have hB := fun k => le_sup_right.trans (hle k)
    exact ⟨(Sec13Restrict.commuting_subgroupOf_iff' (hA i) (hA j)).2 c1,
      (Sec13Restrict.commuting_subgroupOf_iff' (hA i) (hB j)).2 c2,
      (Sec13Restrict.commuting_subgroupOf_iff' (hB i) (hA j)).2 c3,
      (Sec13Restrict.commuting_subgroupOf_iff' (hB i) (hB j)).2 c4⟩
  have hnt : ∃ k, ∃ a ∈ (A k).subgroupOf L, a ≠ 1 := by
    obtain ⟨a, ha, ha1⟩ := hR.exists_ne_one (hX.memA ⟨0, by omega⟩)
    refine ⟨⟨0, by omega⟩, ⟨a, le_sup_left.trans (hle _) ha⟩, ha, fun h => ha1 ?_⟩
    exact congrArg Subtype.val h
  obtain ⟨Ψ, hΨA, hΨB, hsurj, -⟩ := exists_surjective_of_rho (D := Spin.plusDatum n F hn3)
    (CurtisTits.curtisTitsConclusion_spinPlus ⟨Nat.prime_two, hf, hn⟩ hF hn3)
    (leviConePresented_spinPlus F hn3) (simplyLacedLevis_spinPlus F hn3) hnonadj ρ hρ hedge
    (iSup_subgroupOf_eq_top_of_iSup_eq hgen) hnt
  exact ⟨f, hf, Ψ, hΨA, hΨB, hsurj⟩

theorem IsConfig.exists_surjective_A_le [Finite G] (hR : IsRootClass R) (hiso : NoIsolated R)
    {L : Subgroup G} {m : ℕ} (hm : 3 ≤ m) {A B : Fin m → Subgroup G}
    (hX : IsConfig R (edgeA m) A B) (hgen : ⨆ k, (A k ⊔ B k) = L) :
    ∃ f : ℕ, 1 ≤ f ∧
      ∃ Ψ : SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f) →* ↥L,
        (∀ k, ((SpecialLinear.rootDatum m (GaloisField 2 f)).rootGroup (sroot k)).map Ψ =
          (A k).subgroupOf L) ∧
        (∀ k, ((SpecialLinear.rootDatum m (GaloisField 2 f)).rootGroup (-sroot k)).map Ψ =
          (B k).subgroupOf L) ∧ Function.Surjective Ψ := by
  have hle : ∀ k, A k ⊔ B k ≤ L := fun k => hgen ▸ le_iSup (fun k => A k ⊔ B k) k
  obtain ⟨f, hf, ρ, hρ, hedge⟩ := hX.exists_frame_le hR hiso (isRootedTree_A (by omega)) hle
  set F := GaloisField 2 f
  have hF : Nat.card F = 2 ^ f := GaloisField.card 2 f (by omega)
  have hnonadj : ∀ i j, i ≠ j → ¬ edgeA m i j → ¬ edgeA m j i →
      Commuting ((A i).subgroupOf L) ((A j).subgroupOf L) ∧
      Commuting ((A i).subgroupOf L) ((B j).subgroupOf L) ∧
      Commuting ((B i).subgroupOf L) ((A j).subgroupOf L) ∧
      Commuting ((B i).subgroupOf L) ((B j).subgroupOf L) := by
    intro i j hij h1 h2
    obtain ⟨c1, c2, c3, c4⟩ := hX.nonadj i j hij h1 h2
    have hA := fun k => le_sup_left.trans (hle k)
    have hB := fun k => le_sup_right.trans (hle k)
    exact ⟨(Sec13Restrict.commuting_subgroupOf_iff' (hA i) (hA j)).2 c1,
      (Sec13Restrict.commuting_subgroupOf_iff' (hA i) (hB j)).2 c2,
      (Sec13Restrict.commuting_subgroupOf_iff' (hB i) (hA j)).2 c3,
      (Sec13Restrict.commuting_subgroupOf_iff' (hB i) (hB j)).2 c4⟩
  have hnt : ∃ k, ∃ a ∈ (A k).subgroupOf L, a ≠ 1 := by
    obtain ⟨a, ha, ha1⟩ := hR.exists_ne_one (hX.memA ⟨0, by omega⟩)
    refine ⟨⟨0, by omega⟩, ⟨a, le_sup_left.trans (hle _) ha⟩, ha, fun h => ha1 ?_⟩
    exact congrArg Subtype.val h
  obtain ⟨Ψ, hΨA, hΨB, hsurj, -⟩ := exists_surjective_of_rho (D := SpecialLinear.rootDatum m F)
    (CurtisTits.curtisTitsConclusion_specialLinear
      ⟨Nat.prime_two, hf, by omega, fun h => by injection h; omega,
        fun h => by injection h; omega⟩ hF hm)
    (leviConePresented_specialLinear m F) (simplyLacedLevis_specialLinear m F) hnonadj ρ hρ hedge
    (iSup_subgroupOf_eq_top_of_iSup_eq hgen) hnt
  exact ⟨f, hf, Ψ, hΨA, hΨB, hsurj⟩

end CFSG.Timmesfeld.ARS
