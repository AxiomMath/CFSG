module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporAutLocal

public section

namespace CFSG.Quasithin.ModH.LocalPair

open CFSG.QuasithinUnique.Ch1.SporAut

theorem exists_conj_of_local_pair_strong {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (S : Sylow p G) (H : Subgroup G)
    (hH : H = Subgroup.centralizer
      (((Subgroup.center (S : Subgroup G)).map (S : Subgroup G).subtype : Subgroup G) : Set G))
    (K : Subgroup G) (hKS : K ≤ S) (N : Subgroup G) (hN : N = Subgroup.normalizer (K : Set G))
    (J : Subgroup G) (hJp : IsPGroup p J) (hJS : J ≤ S) (hJH : J ≤ H)
    (hJn : (J.subgroupOf H).Normal) (hCJ : H ⊓ Subgroup.centralizer (J : Set G) ≤ J)
    (hCK : N ⊓ Subgroup.centralizer (K : Set G) ≤ K) (hgen : H ⊔ N = ⊤)
    (hSN : (S : Subgroup G) ≤ N)
    (α : MulAut G) (hα : ∀ s ∈ (S : Subgroup G), α s = s) :
    ∃ c : G, c ∈ (Subgroup.center (S : Subgroup G)).map (S : Subgroup G).subtype ∧
      ∀ x, α x = c * x * c⁻¹ := by
  classical
  set Z : Subgroup G := (Subgroup.center (S : Subgroup G)).map (S : Subgroup G).subtype with hZ
  have hZS : ∀ z ∈ Z, α z = z := by
    rintro z ⟨y, -, rfl⟩
    exact hα y y.2
  have hmemZ : ∀ c ∈ (S : Subgroup G), (∀ s ∈ (S : Subgroup G), s * c = c * s) → c ∈ Z := by
    intro c hc hcs
    refine ⟨⟨c, hc⟩, Subgroup.mem_center_iff.2 fun g => Subtype.ext (hcs g g.2), rfl⟩
  have hSH : (S : Subgroup G) ≤ H := by
    intro s hs
    rw [hH, Subgroup.mem_centralizer_iff]
    rintro z ⟨y, hy, rfl⟩
    have := Subgroup.mem_center_iff.1 hy ⟨s, hs⟩
    exact (congrArg Subtype.val this).symm
  have hSdiv : ∀ L : Subgroup G, (S : Subgroup G) ≤ L → ¬ p ∣ (S : Subgroup G).relIndex L := by
    intro L hL hdvd
    exact S.not_dvd_index (dvd_trans hdvd (Subgroup.relIndex_dvd_index_of_le hL))
  have hαH : ∀ x ∈ H, α x ∈ H := by
    intro x hx
    rw [hH, Subgroup.mem_centralizer_iff] at hx ⊢
    intro z hz
    have := hx z hz
    rw [← hZS z hz, ← map_mul, ← map_mul, this]
  have hαK : ∀ k ∈ K, α k = k := fun k hk => hα k (hKS hk)
  have hαKs : ∀ k ∈ K, α.symm k = k := fun k hk => by
    have := congrArg α.symm (hαK k hk)
    simpa using this.symm
  have hαN : ∀ x ∈ N, α x ∈ N := by
    intro x hx
    rw [hN, Subgroup.mem_normalizer_iff] at hx ⊢
    intro h
    have e : α x * h * (α x)⁻¹ = α (x * α.symm h * x⁻¹) := by
      rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
    rw [e]
    constructor
    · intro hh
      rw [hαKs h hh]
      have h2 := (hx h).1 hh
      rw [hαK _ h2]
      exact h2
    · intro hh
      have h3 : x * α.symm h * x⁻¹ ∈ K := by
        have h4 : α (x * α.symm h * x⁻¹) = α (α (x * α.symm h * x⁻¹)) := by
          rw [hαK _ hh]
        rw [α.injective h4]
        exact hh
      have h5 : α.symm h ∈ K := (hx _).2 h3
      have h6 : h = α.symm h := by
        have := hαK _ h5
        rwa [MulEquiv.apply_symm_apply] at this
      rw [h6]
      exact h5
  have hQH : ∀ x ∈ H, ∀ q ∈ J, x * q * x⁻¹ ∈ J := fun x hx q hq =>
    (Subgroup.normal_subgroupOf_iff hJH).1 hJn q x hq hx
  obtain ⟨c1, hc1J, -, hc1⟩ := exists_conj_of_fixing_sylow H J S hJS hJp hQH hCJ
    (hSdiv H hSH) α hαH hα
  have hc1Z : c1 ∈ Z := hmemZ c1 (hJS hc1J) fun s hs => by
    have h := hc1 s (hSH hs)
    rw [hα s hs] at h
    calc s * c1 = c1 * s * c1⁻¹ * c1 := by rw [← h]
      _ = c1 * s := by group
  have hHc : ∀ z ∈ Z, ∀ x ∈ H, z * x = x * z := by
    intro z hz x hx
    rw [hH, Subgroup.mem_centralizer_iff] at hx
    exact hx z hz
  have hαHid : ∀ x ∈ H, α x = x := by
    intro x hx
    rw [hc1 x hx]
    have := hHc c1 hc1Z x hx
    calc c1 * x * c1⁻¹ = x * c1 * c1⁻¹ := by rw [this]
      _ = x := by group
  have hKN : ∀ x ∈ N, ∀ q ∈ K, x * q * x⁻¹ ∈ K := by
    intro x hx q hq
    rw [hN, Subgroup.mem_normalizer_iff] at hx
    exact (hx q).1 hq
  obtain ⟨c2, hc2K, -, hc2⟩ := exists_conj_of_fixing_sylow N K S hKS
    (IsPGroup.to_le S.isPGroup' hKS) hKN hCK (hSdiv N hSN) α hαN hα
  have hc2Z : c2 ∈ Z := hmemZ c2 (hKS hc2K) fun s hs => by
    have h := hc2 s (hSN hs)
    rw [hα s hs] at h
    calc s * c2 = c2 * s * c2⁻¹ * c2 := by rw [← h]
      _ = c2 * s := by group
  refine ⟨c2, hc2Z, fun x => ?_⟩
  have hle : H ⊔ N ≤ MonoidHom.eqLocus (α : G →* G) (MulAut.conj c2 : G →* G) := by
    refine sup_le (fun y hy => ?_) (fun y hy => ?_)
    · change α y = c2 * y * c2⁻¹
      rw [hαHid y hy]
      have := hHc c2 hc2Z y hy
      calc y = y * c2 * c2⁻¹ := by group
        _ = c2 * y * c2⁻¹ := by rw [this]
    · exact hc2 y hy
  exact hle (by rw [hgen]; trivial)

end CFSG.Quasithin.ModH.LocalPair
