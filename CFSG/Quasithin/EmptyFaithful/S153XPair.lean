module

public import CFSG.Quasithin.EmptyFaithful.S153XLoc
public import CFSG.Quasithin.EmptyFaithful.S153VIz
import CFSG.Quasithin.EmptyFaithful.S153WJ
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InA3Conj

public section

namespace CFSG.Quasithin.X1469

open scoped Pointwise
open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.ModF CFSG.Quasithin.ModV
  CFSG.LieType.BorelTits

variable {G : Type} [Group G]

namespace Pair

theorem conj_mem_of_conjSub_eq {a x : G} {X Y : Subgroup G} (h : B6.conjSub a X = Y) (hx : x ∈ X) :
    a * x * a⁻¹ ∈ Y := by
  rw [← h, B6.mem_conjSub]
  have e : a⁻¹ * (a * x * a⁻¹) * a = x := by group
  rw [e]
  exact hx

theorem inv_conj_mem_of_conjSub_eq {a y : G} {X Y : Subgroup G} (h : B6.conjSub a X = Y) (hy : y ∈ Y) :
    a⁻¹ * y * a ∈ X := by
  rw [← h, B6.mem_conjSub] at hy
  exact hy

theorem conjSub_blockU {a : G} {L L' : Subgroup G} (h : B6.conjSub a L = L') :
    B6.conjSub a (blockU L) = blockU L' := by
  have e : blockU (B6.conjSub a L) = B6.conjSub a (blockU L) :=
    Lin2.blockU_map_equiv (MulAut.conj a) L
  rw [← e, h]

theorem conjSub_inf {a : G} {S L L' : Subgroup G} (ha : a ∈ Subgroup.normalizer (S : Set G))
    (h : B6.conjSub a L = L') : B6.conjSub a (S ⊓ L) = S ⊓ L' := by
  rw [OrderIso.map_inf, B6.conjSub_eq_self ha, h]

theorem conjSub_Esub {a : G} {L Iz : Subgroup G} (ha : a ∈ Subgroup.normalizer (Iz : Set G)) :
    B6.conjSub a (Esub L Iz) = Esub (B6.conjSub a L) Iz := by
  have hU : blockU (B6.conjSub a L) = B6.conjSub a (blockU L) :=
    Lin2.blockU_map_equiv (MulAut.conj a) L
  have hY : B6.conjSub a (L ⊓ Iz) = B6.conjSub a L ⊓ Iz := by
    rw [OrderIso.map_inf, B6.conjSub_eq_self ha]
  have hc : B6.conjSub a (Esub L Iz) = ⁅B6.conjSub a (blockU L), B6.conjSub a (L ⊓ Iz)⁆ :=
    Subgroup.map_commutator (blockU L) (L ⊓ Iz) (MulAut.conj a).toMonoidHom
  rw [hc, ← hU, hY]

theorem eq_one_of_mem_dsub {S K₁ K₂ : Subgroup G}
    (hD : S ⊓ Subgroup.centralizer ((K₁ ⊔ K₂ : Subgroup G) : Set G) = ⊥) {d : G}
    (hd : d ∈ dsub S K₁ K₂) : d = 1 := by
  have hd' : d ∈ S ⊓ Subgroup.centralizer ((K₁ ⊔ K₂ : Subgroup G) : Set G) := hd
  rw [hD] at hd'
  exact Subgroup.mem_bot.mp hd'

variable {I S Iz K₁ K₂ : Subgroup G}

theorem conjSub_eq_or (c : A5Cfg I S Iz K₁ K₂) {g : G} (hg : g ∈ I) :
    B6.conjSub g K₁ = K₁ ∨ B6.conjSub g K₁ = K₂ := by
  have hg' : g ∈ ((S : Subgroup G) : Set G) * ((K₁ ⊔ K₂ : Subgroup G) : Set G) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right S (K₁ ⊔ K₂) c.S_le_normalizer_sup, ← c.gen]
    exact hg
  obtain ⟨s, hs, k, hk, rfl⟩ := hg'
  have hk' : k ∈ ((K₁ : Subgroup G) : Set G) * ((K₂ : Subgroup G) : Set G) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right K₁ K₂ c.K₁_le_normalizer₂]
    exact hk
  obtain ⟨k₁, hk₁, k₂, hk₂, rfl⟩ := hk'
  have hN₂ : k₂ ∈ Subgroup.normalizer (K₁ : Set G) :=
    Lin2.le_normalizer_of_commute (A := K₁) (B := K₂) (fun a ha b hb => c.comm a ha b hb) hk₂
  have e : B6.conjSub (s * (k₁ * k₂)) K₁ = B6.conjSub s K₁ := by
    rw [B6.conjSub_mul, B6.conjSub_mul, B6.conjSub_eq_self hN₂,
      B6.conjSub_eq_self (Subgroup.le_normalizer hk₁)]
  rw [e]
  exact c.perm₁ s hs

theorem Iz_le_normalizer_E0 (c : A5Cfg I S Iz K₁ K₂) :
    Iz ≤ Subgroup.normalizer ((E0 K₁ K₂ Iz : Subgroup G) : Set G) := by
  have key : ∀ g ∈ Iz, B6.conjSub g (E0 K₁ K₂ Iz) ≤ E0 K₁ K₂ Iz := by
    intro g hg
    have hgN : g ∈ Subgroup.normalizer (Iz : Set G) := Subgroup.le_normalizer hg
    have hgI : g ∈ I := c.Iz_le_I hg
    have h₁ : B6.conjSub g (Esub K₁ Iz) ≤ E0 K₁ K₂ Iz := by
      rw [conjSub_Esub hgN]
      rcases conjSub_eq_or c hgI with h | h <;> rw [h]
      · exact le_sup_left
      · exact le_sup_right
    have h₂ : B6.conjSub g (Esub K₂ Iz) ≤ E0 K₁ K₂ Iz := by
      rw [conjSub_Esub hgN]
      rcases conjSub_eq_or c.symm hgI with h | h <;> rw [h]
      · exact le_sup_right
      · exact le_sup_left
    show B6.conjSub g (Esub K₁ Iz ⊔ Esub K₂ Iz) ≤ Esub K₁ Iz ⊔ Esub K₂ Iz
    rw [OrderIso.map_sup]
    exact sup_le h₁ h₂
  intro g hg
  exact B6.mem_normalizer_of_conjSub_le (key g hg) (key g⁻¹ (Iz.inv_mem hg))

variable [Finite G]

theorem Zsub_le_z0 (c : A5Cfg I S Iz K₁ K₂)
    (hD : S ⊓ Subgroup.centralizer ((K₁ ⊔ K₂ : Subgroup G) : Set G) = ⊥) : Zsub S K₁ ≤ z0 Iz := by
  intro x hx
  obtain ⟨hxU, hxC⟩ := hx
  have hxR : x ∈ pCoreOf 2 Iz := c.blockU₁_le_R hxU
  have hx2 : x ^ 2 = 1 := (AppC.isElemAbelian_blockU c.blk₁.1).2 x hxU
  have hxZ : x ∈ centerOf (pCoreOf 2 Iz) := by
    refine ⟨hxR, Subgroup.mem_centralizer_iff.mpr fun g hg => ?_⟩
    obtain ⟨d, hd, s₁, hs₁, s₂, hs₂, rfl⟩ := c.exists_decomp_R hg
    rw [eq_one_of_mem_dsub hD hd, one_mul]
    have h₁ : s₁ * x = x * s₁ := Subgroup.mem_centralizer_iff.mp hxC s₁ hs₁
    have h₂ : x * s₂ = s₂ * x := c.comm x (c.U₁_le_K₁ hxU) s₂ hs₂.2
    calc s₁ * s₂ * x = s₁ * (s₂ * x) := by group
      _ = s₁ * (x * s₂) := by rw [h₂]
      _ = (s₁ * x) * s₂ := by group
      _ = (x * s₁) * s₂ := by rw [h₁]
      _ = x * (s₁ * s₂) := by group
  show x ∈ Subgroup.closure {y | y ∈ centerOf (pCoreOf 2 Iz) ∧ y ^ 2 = 1}
  exact Subgroup.subset_closure ⟨hxZ, hx2⟩

end Pair

theorem exists_pairGen [Finite G] {I S Iz K₁ K₂ T : Subgroup G} {r z : G}
    (C : LocalCfg I S Iz K₁ K₂ T r z) : ∃ t : G, PairGen I S Iz K₁ K₂ t z := by
  obtain ⟨t, htS, htK⟩ := C.ht
  have c := C.cfg
  have htIz : t ∈ Iz := c.S_le_Iz htS
  have htN : t ∈ Subgroup.normalizer (Iz : Set G) := Subgroup.le_normalizer htIz
  have htNS : t ∈ Subgroup.normalizer (S : Set G) := Subgroup.le_normalizer htS
  have hnot₂ : ¬ K₂ ≤ Iz := by
    intro h₂
    apply C.hnot
    intro k hk
    have h₁ := Iz.mul_mem (Iz.mul_mem (Iz.inv_mem htIz) (h₂ (Pair.conj_mem_of_conjSub_eq htK hk))) htIz
    have e : t⁻¹ * (t * k * t⁻¹) * t = k := by group
    rwa [e] at h₁
  have hU : B6.conjSub t (blockU K₁) = blockU K₂ := Pair.conjSub_blockU htK
  have hB : B6.conjSub t (S ⊓ K₁) = S ⊓ K₂ := Pair.conjSub_inf htNS htK
  have hE : B6.conjSub t (Esub K₁ Iz) = Esub K₂ Iz := by rw [Pair.conjSub_Esub htN, htK]
  have hD' : S ⊓ Subgroup.centralizer ((K₂ ⊔ K₁ : Subgroup G) : Set G) = ⊥ := by
    rw [sup_comm]
    exact C.hD
  have hP := c.P_le_pCoreIz C.hnot hnot₂
  refine ⟨t, ⟨htS, htK, c.comm, hnot₂, c.S_le_Iz, c.R_le_S, le_normalizer_pCoreOf 2 Iz,
    c.Iz_le_I.trans (le_normalizer_pCoreOf 2 I),
    fun k hk => C1.mem_normalizer_blockU (Subgroup.le_normalizer hk),
    fun k hk => C1.mem_normalizer_blockU (Subgroup.le_normalizer hk),
    AppC.isElemAbelian_blockU c.blk₁.1, AppC.isElemAbelian_blockU c.blk₂.1, c.blockU_inf_blockU,
    fun u hu => ⟨c.sylow.pCoreOf_le (c.U₁_le_pCoreI hu), c.U₁_le_K₁ hu⟩,
    fun u hu => ⟨c.sylow.pCoreOf_le (c.U₂_le_pCoreI hu), c.U₂_le_K₂ hu⟩,
    le_sup_left.trans hP, le_sup_right.trans hP, c.Q_le_R, c.U₁_le_pCoreI, c.U₂_le_pCoreI,
    ?_, ?_,
    fun u hu => Pair.conj_mem_of_conjSub_eq hU hu, fun u hu => Pair.inv_conj_mem_of_conjSub_eq hU hu,
    fun b hb => Pair.conj_mem_of_conjSub_eq hB hb, fun b hb => Pair.inv_conj_mem_of_conjSub_eq hB hb,
    fun e he => Pair.conj_mem_of_conjSub_eq hE he, fun e he => Pair.inv_conj_mem_of_conjSub_eq hE he,
    Pair.Iz_le_normalizer_E0 c, Pair.Zsub_le_z0 c C.hD, Pair.Zsub_le_z0 c.symm hD', ?_⟩⟩
  · intro g hg
    obtain ⟨d, hd, u₁, hu₁, u₂, hu₂, rfl⟩ := c.exists_split_Q hg
    exact ⟨u₁, hu₁, u₂, hu₂, by rw [Pair.eq_one_of_mem_dsub C.hD hd, one_mul]⟩
  · intro g hg
    obtain ⟨d, hd, s₁, hs₁, s₂, hs₂, rfl⟩ := c.exists_decomp_R hg
    exact ⟨s₁, hs₁, s₂, hs₂, by rw [Pair.eq_one_of_mem_dsub C.hD hd, one_mul]⟩
  · have hzI : z ∈ I := c.sylow.le C.hzS
    have hcent : z ∈ Subgroup.centralizer ((pCoreOf 2 I : Subgroup G) : Set G) :=
      Subgroup.mem_centralizer_iff.mpr fun h hh => C.hzc h (C.hST (c.sylow.pCoreOf_le hh))
    exact C.charTwo ⟨hzI, hcent⟩

end CFSG.Quasithin.X1469
