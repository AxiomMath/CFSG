module

public import CFSG.Quasithin.EmptyFaithful.S151U4

public section

namespace CFSG.Quasithin.S151TB

open CFSG.QuasithinUnique

theorem hom_trivial_of_odd_index {X Z : Type*} [Group X] [Group Z] [Finite Z] (hZ : IsPGroup 2 Z)
    {S B : Subgroup X} (hBS : B ≤ S) (hodd : ¬ 2 ∣ B.index) (c : ↥S →* Z)
    (hB : ∀ (b : X) (hb : b ∈ B), c ⟨b, hBS hb⟩ = 1) (s : ↥S) : c s = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hZ
  have hBle : B.subgroupOf S ≤ c.ker := fun b hb => MonoidHom.mem_ker.mpr (hB b hb)
  have h1 : c.ker.index ∣ (B.subgroupOf S).index := Subgroup.index_dvd_of_le hBle
  have h2 : (B.subgroupOf S).index ∣ B.index := Subgroup.relIndex_dvd_index_of_le hBS
  have h3 : c.ker.index ∣ 2 ^ n := by
    rw [Subgroup.index_ker, ← hn]
    exact Subgroup.card_subgroup_dvd_card _
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h3
  have hi0 : i = 0 := by
    by_contra hne
    apply hodd
    have h2d : 2 ∣ c.ker.index := by
      rw [hi]
      exact dvd_pow_self 2 hne
    exact h2d.trans (h1.trans h2)
  have hind : c.ker.index = 1 := by rw [hi, hi0, pow_zero]
  have htop : c.ker = ⊤ := Subgroup.index_eq_one.mp hind
  have hs : s ∈ c.ker := by
    rw [htop]
    exact Subgroup.mem_top s
  exact MonoidHom.mem_ker.mp hs

theorem stabilizer_index_le {X : Type*} [Group X] {Ω : Type*} [MulAction X Ω] [Finite Ω]
    (o : Ω) (ho : ∀ g : X, g • o = o) {ω : Ω} (hω : ω ≠ o) :
    (MulAction.stabilizer X ω).index ≤ Nat.card Ω - 1 := by
  classical
  have hidx : Nat.card (MulAction.orbit X ω) = (MulAction.stabilizer X ω).index :=
    Nat.card_congr (MulAction.orbitEquivQuotientStabilizer X ω)
  have horbsub : MulAction.orbit X ω ⊆ ({o}ᶜ : Set Ω) := by
    rintro _ ⟨g, rfl⟩ h
    apply hω
    have h' : g • ω = o := h
    have : ω = g⁻¹ • o := by rw [← h']; simp
    rw [this, ho]
  have hcompl : (({o}ᶜ : Set Ω)).ncard = Nat.card Ω - 1 := by
    have := Set.ncard_compl ({o} : Set Ω)
    rw [Set.ncard_singleton] at this
    exact this
  rw [← hidx, Nat.card_coe_set_eq]
  calc (MulAction.orbit X ω).ncard ≤ (({o}ᶜ : Set Ω)).ncard := Set.ncard_le_ncard horbsub
    _ = Nat.card Ω - 1 := hcompl

theorem commutator_mul_aux {G : Type} [Group G] {L : Subgroup G} (hsh : IsShort2 L) {u l m : G}
    (hl : l ∈ L) (hm : (m * u * m⁻¹)⁻¹ * u ∈ blockZ L) (hl' : (l * u * l⁻¹)⁻¹ * u ∈ blockZ L) :
    ((l * m) * u * (l * m)⁻¹)⁻¹ * u = ((l * u * l⁻¹)⁻¹ * u) * ((m * u * m⁻¹)⁻¹ * u) := by
  have e : ((l * m) * u * (l * m)⁻¹)⁻¹ * u =
      (l * ((m * u * m⁻¹)⁻¹ * u) * l⁻¹) * ((l * u * l⁻¹)⁻¹ * u) := by group
  rw [e, s151v_blockZ_comm hm hl]
  exact s151v_blockU_comm hsh _ (s151v_blockZ_le_blockU L hm) _ (s151v_blockZ_le_blockU L hl')

theorem commute_of_smul_fixed {G : Type} [Group G] [Finite G] {L B : Subgroup G}
    (hsh : IsShort2 L) (hB : IsSylowTwoOf B L) {u : G} (hu : u ∈ blockU L)
    (hBu : ∀ s ∈ B, s * u * s⁻¹ = u) (l : ↥L)
    (hl : l • ((⟨u, hu⟩ : ↥(blockU L)) : BlockN L) = ((⟨u, hu⟩ : ↥(blockU L)) : BlockN L)) :
    (l : G) * u * (l : G)⁻¹ = u := by
  classical
  have hZ2 : IsPGroup 2 ↥(blockZ L) := by
    intro z
    refine ⟨1, ?_⟩
    apply Subtype.ext
    have := s151v_blockU_sq hsh (z : G) (s151v_blockZ_le_blockU L z.2)
    simpa using this
  have hstab : ∀ m : ↥L, m • ((⟨u, hu⟩ : ↥(blockU L)) : BlockN L) =
      ((⟨u, hu⟩ : ↥(blockU L)) : BlockN L) → ((m : G) * u * (m : G)⁻¹)⁻¹ * u ∈ blockZ L := by
    intro m hm
    rw [s151u_smul_mk, s151u_mk_eq_iff] at hm
    exact hm
  have hd : ∀ m : ↥(MulAction.stabilizer ↥L ((⟨u, hu⟩ : ↥(blockU L)) : BlockN L)),
      (((m : ↥L) : G) * u * ((m : ↥L) : G)⁻¹)⁻¹ * u ∈ blockZ L := fun m =>
    hstab m (MulAction.mem_stabilizer_iff.mp m.2)
  let c : ↥(MulAction.stabilizer ↥L ((⟨u, hu⟩ : ↥(blockU L)) : BlockN L)) →* ↥(blockZ L) :=
    MonoidHom.mk' (fun m => ⟨(((m : ↥L) : G) * u * ((m : ↥L) : G)⁻¹)⁻¹ * u, hd m⟩) (fun m n => by
      apply Subtype.ext
      exact commutator_mul_aux hsh (m : ↥L).2 (hd n) (hd m))
  have hBS : B.subgroupOf L ≤
      MulAction.stabilizer ↥L ((⟨u, hu⟩ : ↥(blockU L)) : BlockN L) := by
    intro b hb
    rw [MulAction.mem_stabilizer_iff, s151u_smul_mk]
    congr 1
    exact Subtype.ext (hBu (b : G) hb)
  have hc1 : ∀ (b : ↥L) (hb : b ∈ B.subgroupOf L), c ⟨b, hBS hb⟩ = 1 := by
    intro b hb
    apply Subtype.ext
    show (((b : ↥L) : G) * u * ((b : ↥L) : G)⁻¹)⁻¹ * u = 1
    rw [hBu (b : G) hb]
    simp
  have key := hom_trivial_of_odd_index (X := ↥L) hZ2 hBS hB.2.2 c hc1
    ⟨l, MulAction.mem_stabilizer_iff.mpr hl⟩
  have key' : ((l : G) * u * (l : G)⁻¹)⁻¹ * u = 1 := congrArg Subtype.val key
  exact inv_mul_eq_one.mp key'

theorem index_centralizer_le {G : Type} [Group G] [Finite G] {L B : Subgroup G}
    (hsh : IsShort2 L) (hB : IsSylowTwoOf B L) {u : G} (hu : u ∈ blockU L) (huZ : u ∉ blockZ L)
    (hBu : ∀ s ∈ B, s * u * s⁻¹ = u) :
    (L ⊓ Subgroup.centralizer ({u} : Set G)).relIndex L ≤ Nat.card (BlockN L) - 1 := by
  classical
  have hstab_eq : (L ⊓ Subgroup.centralizer ({u} : Set G)).subgroupOf L =
      MulAction.stabilizer ↥L ((⟨u, hu⟩ : ↥(blockU L)) : BlockN L) := by
    ext l
    rw [Subgroup.mem_subgroupOf, MulAction.mem_stabilizer_iff, Subgroup.mem_inf]
    constructor
    · rintro ⟨-, h⟩
      have hc : u * (l : G) = (l : G) * u := Subgroup.mem_centralizer_iff.mp h u rfl
      rw [s151u_smul_mk]
      congr 1
      apply Subtype.ext
      show (l : G) * u * (l : G)⁻¹ = u
      rw [← hc]
      group
    · intro hl
      refine ⟨l.2, Subgroup.mem_centralizer_iff.mpr fun h hh => ?_⟩
      rw [Set.mem_singleton_iff.mp hh]
      have := commute_of_smul_fixed hsh hB hu hBu l hl
      calc u * (l : G) = ((l : G) * u * (l : G)⁻¹) * (l : G) := by rw [this]
        _ = (l : G) * u := by group
  have hωo : ((⟨u, hu⟩ : ↥(blockU L)) : BlockN L) ≠ ((1 : ↥(blockU L)) : BlockN L) := by
    intro h
    rw [s151u_mk_eq_iff] at h
    apply huZ
    have : u⁻¹ ∈ blockZ L := by simpa using h
    simpa using (blockZ L).inv_mem this
  have ho : ∀ g : ↥L, g • ((1 : ↥(blockU L)) : BlockN L) = ((1 : ↥(blockU L)) : BlockN L) := by
    intro g
    rw [s151u_smul_mk]
    congr 1
    apply Subtype.ext
    simp
  have hidx : (L ⊓ Subgroup.centralizer ({u} : Set G)).relIndex L =
      (MulAction.stabilizer ↥L ((⟨u, hu⟩ : ↥(blockU L)) : BlockN L)).index := by
    rw [← hstab_eq]
    rfl
  rw [hidx]
  exact stabilizer_index_le ((1 : ↥(blockU L)) : BlockN L) ho hωo

theorem isMaxSubgroupIn_of_relIndex_le {G : Type} [Group G] [Finite G] {L B P : Subgroup G}
    {n : ℕ} (hBP : B ≤ P) (hPL : P < L)
    (hmax3 : ∀ H : Subgroup G, IsMaxSubgroupIn L H → B ≤ H → Nat.card H = 3 * Nat.card B)
    (hcard : Nat.card ↥L = 3 * Nat.card B * n) (hn : 0 < n) (hidx : P.relIndex L ≤ n) :
    IsMaxSubgroupIn L P := by
  have hcardL : Nat.card ↥L = Nat.card ↥P * P.relIndex L := by
    have h1 := Subgroup.card_mul_index (P.subgroupOf L)
    have h2 : Nat.card ↥(P.subgroupOf L) = Nat.card ↥P :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPL.le).toEquiv
    rw [← h1, h2]
    rfl
  obtain ⟨K, hK, hPK⟩ := exists_isMaxSubgroupIn hPL
  have hKcard : Nat.card ↥K = 3 * Nat.card ↥B := hmax3 K hK (hBP.trans hPK)
  have hle : Nat.card ↥K ≤ Nat.card ↥P := by
    refine Nat.le_of_mul_le_mul_right ?_ hn
    calc Nat.card ↥K * n = Nat.card ↥L := by rw [hKcard, hcard]
      _ = Nat.card ↥P * P.relIndex L := hcardL
      _ ≤ Nat.card ↥P * n := Nat.mul_le_mul_left _ hidx
  have hPK' : P = K := Subgroup.eq_of_le_of_card_ge hPK hle
  rw [hPK']
  exact hK

theorem rank2_centralizer_max {G : Type} [Group G] [Finite G] {L B W : Subgroup G}
    (hsh : IsShort2 L) (hB : IsSylowTwoOf B L)
    (hN : L ⊓ Subgroup.normalizer (B : Set G) ≤ B)
    (hmax3 : ∀ H : Subgroup G, IsMaxSubgroupIn L H → B ≤ H → Nat.card H = 3 * Nat.card B)
    (hcard : Nat.card ↥L = 3 * Nat.card B * (Nat.card (BlockN L) - 1))
    (hbig : 4 ≤ Nat.card (BlockN L))
    (hW : W ≤ blockU L) (hWB : ∀ w ∈ W, ∀ s ∈ B, s * w * s⁻¹ = w)
    (hnot : ¬ L ≤ Subgroup.centralizer (W : Set G)) :
    B ≤ L ⊓ Subgroup.centralizer (W : Set G) ∧
      IsMaxSubgroupIn L (L ⊓ Subgroup.centralizer (W : Set G)) := by
  classical
  have hBL : B ≤ L := hB.1
  have hBP : B ≤ L ⊓ Subgroup.centralizer (W : Set G) := by
    intro s hs
    refine ⟨hBL hs, Subgroup.mem_centralizer_iff.mpr fun w hw => ?_⟩
    have h := hWB w hw s hs
    calc w * s = (s * w * s⁻¹) * s := by rw [h]
      _ = s * w := by group
  obtain ⟨u, huW, huZ⟩ : ∃ u ∈ W, u ∉ blockZ L := by
    by_contra h
    push Not at h
    apply hnot
    intro l hl
    refine Subgroup.mem_centralizer_iff.mpr fun w hw => ?_
    have h1 := s151v_blockZ_comm (h w hw) hl
    calc w * l = (l * w * l⁻¹) * l := by rw [h1]
      _ = l * w := by group
  have hcases : ∀ w ∈ W, w ∈ blockZ L ∨ u⁻¹ * w ∈ blockZ L := by
    intro w hw
    by_cases hwZ : w ∈ blockZ L
    · exact Or.inl hwZ
    · refine Or.inr (s151u_fix_le_two hsh hB hN hmax3 hcard hbig u (hW huW) w (hW hw) huZ hwZ
        (fun s hs => ?_) (fun s hs => ?_))
      · rw [hWB u huW s hs]
        simp
      · rw [hWB w hw s hs]
        simp
  have hPeq : L ⊓ Subgroup.centralizer (W : Set G) = L ⊓ Subgroup.centralizer ({u} : Set G) := by
    apply le_antisymm
    · exact inf_le_inf_left L (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr huW))
    · rintro l ⟨hl, hlu⟩
      refine ⟨hl, Subgroup.mem_centralizer_iff.mpr fun w hw => ?_⟩
      have hul : u * l = l * u := Subgroup.mem_centralizer_iff.mp hlu u rfl
      have hlu' : l * u * l⁻¹ = u := by rw [← hul]; group
      have hlw : l * w * l⁻¹ = w := by
        rcases hcases w hw with h | h
        · exact s151v_blockZ_comm h hl
        · have hz := s151v_blockZ_comm h hl
          calc l * w * l⁻¹ = (l * u * l⁻¹) * (l * (u⁻¹ * w) * l⁻¹) := by group
            _ = u * (u⁻¹ * w) := by rw [hlu', hz]
            _ = w := by group
      calc w * l = (l * w * l⁻¹) * l := by rw [hlw]
        _ = l * w := by group
  have hPL : L ⊓ Subgroup.centralizer (W : Set G) < L :=
    lt_of_le_of_ne inf_le_left fun h => hnot (inf_eq_left.mp h)
  have hidx : (L ⊓ Subgroup.centralizer (W : Set G)).relIndex L ≤ Nat.card (BlockN L) - 1 := by
    rw [hPeq]
    exact index_centralizer_le hsh hB (hW huW) huZ (hWB u huW)
  exact ⟨hBP, isMaxSubgroupIn_of_relIndex_le hBP hPL hmax3 hcard (by omega) hidx⟩

end CFSG.Quasithin.S151TB
