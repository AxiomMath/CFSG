module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86AsmLOrb
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8Hyp
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P2KBall

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace AsmL

theorem fan512_aux (F : FanTree Γ G) (L : ZLab Γ G) {α : V} {z : G} (hα : valence Γ α = 5)
    (hLz : L.z α = z) (hnone : ∀ β : V, ¬ Equiv3 G α β → Cinv G β = ∅)
    (hball : z ∈ ballStab Γ G 2 α)
    (hprod : ∀ (β : V) (l : List V) (h : V → G), ¬ Equiv3 G α β → l.Nodup →
      (∀ u, u ∈ l ↔ Γ.Adj β u) → (∀ u, Γ.Adj β u → h u • α = u) →
      (l.map fun u => h u * z * (h u)⁻¹).Pairwise Commute ∧
        (l.map fun u => h u * z * (h u)⁻¹).prod = 1)
    (huniq : ∀ (g : G) (α' : V), g • α = α' → Cinv G α' = {g * z * g⁻¹}) : Fan512 F L := by
  have hne : ∀ β : V, valence Γ β = 3 → ¬ Equiv3 G α β := fun β hβ => by
    rintro ⟨g, hg⟩
    have := F.valence_smul_eq g α
    rw [hg, hβ, hα] at this
    omega
  refine ⟨fun β hβ z' hz'st hz'c hz'sq => ?_, fun v hv => ?_, fun β a b c hβ hset hab hac hbc => ?_,
    fun v hv w hw => ?_⟩
  · by_contra h1
    have : z' ∈ Cinv G β := ⟨h1, hz'sq, hz'st, hz'c⟩
    rw [hnone β (hne β hβ)] at this
    exact this
  · obtain ⟨g, hg, hz⟩ := exists_conj F L hα hv
    rw [hz, hLz, ← hg]
    exact (Sec8P2K.mem_ballStab_smul_iff F 2 g α).2
      (by rw [show g⁻¹ * (g * z * g⁻¹) * g = z by group]; exact hball)
  · have hmem : ∀ u, u ∈ [a, b, c] ↔ Γ.Adj β u := by
      intro u
      have : u ∈ Γ.neighborSet β ↔ u ∈ ({a, b, c} : Set V) := by rw [hset]
      simpa [or_assoc] using this.symm
    have hfun : ∀ u, Γ.Adj β u → P62.pick G α u • α = u := by
      intro u hu
      obtain ⟨g, hg⟩ := P62.exists_smul_of_valence_eq F (u := α) (w := u)
        (by rw [F.val5_of_adj_val3 hu hβ, hα])
      exact P62.pick_smul ⟨g, hg⟩
    have hlab : ∀ u, Γ.Adj β u → L.z u = P62.pick G α u * z * (P62.pick G α u)⁻¹ := fun u hu => by
      have := L.equivariant (P62.pick G α u) α hα
      rwa [hfun u hu, hLz] at this
    obtain ⟨-, hp⟩ := hprod β [a, b, c] (P62.pick G α) (hne β hβ) (by simp [hab, hac, hbc]) hmem
      hfun
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at hp
    rw [← mul_assoc] at hp
    rw [hlab a ((hmem a).1 (by simp)), hlab b ((hmem b).1 (by simp)),
      hlab c ((hmem c).1 (by simp))]
    exact hp
  · obtain ⟨g, hg, hz⟩ := exists_conj F L hα hv
    have hwm : w ∈ Cinv G v := P62.cinv_iff.2 hw
    rw [huniq g v hg] at hwm
    rw [hz, hLz]
    exact hwm

end AsmL

theorem fan512_of_lab (F : FanTree Γ G) (h40 : Fan40 F) (h512a : Fan512a F) (h512b : Fan512b F)
    (h512d : Fan512d F) (L : ZLab Γ G) (T : Track Γ G) (hT : InXi T) (a : ℤ) {z : G}
    (hZ : z ∈ T.line.ZZ) (hz1 : z ≠ 1) (hcore : T.line.IsCore z a (a + 2))
    (hα : valence Γ (T.line.vert (a + 1)) = 5) (hLz : L.z (T.line.vert (a + 1)) = z) :
    Fan512 F L :=
  AsmL.fan512_aux F L hα hLz (h512a h40 T z a hT hZ hz1 hcore)
    (h512b h40 T z a hT hZ hz1 hcore).1 (fun β l h => (h512b h40 T z a hT hZ hz1 hcore).2 β l h)
    (fun g α' hg => h512d h40 T z a hT hZ hz1 hcore g α' hg)

end CFSG.Quasithin.Fan86
