module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS143W2CompE

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1
  CFSG.QuasithinUnique.Tight CFSG.QuasithinUnique.BenderBranch
  CFSG.ComponentClassification.AschbacherTightEmbedding

namespace S143

namespace InspW2

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {g : G} {A : Subgroup G} {t d x : G}
  {Z : Subgroup G}

theorem Ctx.orderOf_w (h : Ctx T M g A t d x) : orderOf (wOfX d x) = 2 :=
  orderOf_eq_prime (by rw [pow_two]; exact h.w_sq) h.w_ne

theorem card_le_four_of_le (h : Ctx T M g A t d x) (hf : Wp0 T d x)
    (hZn : ∀ u ∈ K0 T d x, ∀ k ∈ Z, u * k * u⁻¹ ∈ Z) (hz : d * d ∉ Z) {S : Subgroup G}
    (hS : S ≤ Tw T d x ⊓ Z) : Nat.card S ≤ 4 := by
  have hSB : S ≤ Bw T d x := fun s hs =>
    Z_inf_Cw_le_Bw h hf hZn hz ⟨(hS hs).2, h.Tw_le_Cw (hS hs).1⟩
  have hSu : S ⊓ Subgroup.zpowers (u0Of d x) = ⊥ := by
    rw [eq_bot_iff]
    rintro s ⟨hsS, hsu⟩
    have hK : s ∈ K0 T d x := (Subgroup.zpowers_le.mpr h.u0_mem_K0) hsu
    have h1 : s ∈ K0 T d x ⊓ Z := ⟨hK, (hS hsS).2⟩
    rw [K0_inf_eq_bot hf hZn hz] at h1
    exact h1
  have hww : wOfX d x ∈ Subgroup.centralizer (Subgroup.zpowers (u0Of d x) : Set G) := by
    refine Subgroup.mem_centralizer_iff.mpr fun v hv => ?_
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
    exact (Commute.zpow_left (show Commute (u0Of d x) (wOfX d x) from h.u0_comm_w) k).eq
  have huu : u0Of d x ∈ Subgroup.centralizer (Subgroup.zpowers (u0Of d x) : Set G) := by
    refine Subgroup.mem_centralizer_iff.mpr fun v hv => ?_
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
    exact (Commute.zpow_left (Commute.refl (u0Of d x)) k).eq
  have hAcent : Subgroup.zpowers (u0Of d x) ⊔ Subgroup.zpowers (wOfX d x) ≤
      Subgroup.centralizer (Subgroup.zpowers (u0Of d x) : Set G) :=
    sup_le (Subgroup.zpowers_le.mpr huu) (Subgroup.zpowers_le.mpr hww)
  have hu0w : Subgroup.zpowers (u0Of d x) ≤
      Subgroup.centralizer (Subgroup.zpowers (wOfX d x) : Set G) := by
    refine Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_iff.mpr fun v hv => ?_)
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
    exact (Commute.zpow_left (show Commute (wOfX d x) (u0Of d x) from h.u0_comm_w.symm) k).eq
  have hA0card : Nat.card ↥(Subgroup.zpowers (u0Of d x) ⊔ Subgroup.zpowers (wOfX d x)) ≤ 8 := by
    have h1 := card_sup_mul_card_inf_of_le_centralizer hu0w
    rw [Nat.card_zpowers, Nat.card_zpowers, h.orderOf_u0, h.orderOf_w] at h1
    have : 0 < Nat.card ↥(Subgroup.zpowers (u0Of d x) ⊓ Subgroup.zpowers (wOfX d x)) :=
      Nat.card_pos
    nlinarith
  have hBA : S ⊓ qOf T ≤ Subgroup.zpowers (u0Of d x) ⊔ Subgroup.zpowers (wOfX d x) :=
    fun b hb => hf.Bw_inf_Q ⟨hSB hb.1, hb.2⟩
  have hBu : (S ⊓ qOf T) ⊓ Subgroup.zpowers (u0Of d x) = ⊥ := by
    rw [eq_bot_iff, ← hSu]
    exact inf_le_inf_right _ inf_le_left
  have hBcard : Nat.card ↥(S ⊓ qOf T) ≤ 2 := by
    have h1 := card_sup_mul_card_inf_of_le_centralizer (A := S ⊓ qOf T)
      (B := Subgroup.zpowers (u0Of d x)) (hBA.trans hAcent)
    rw [hBu, Subgroup.card_bot, Nat.card_zpowers, h.orderOf_u0] at h1
    have hle : Nat.card ↥((S ⊓ qOf T) ⊔ Subgroup.zpowers (u0Of d x)) ≤
        Nat.card ↥(Subgroup.zpowers (u0Of d x) ⊔ Subgroup.zpowers (wOfX d x)) :=
      Subgroup.card_le_of_le (sup_le hBA le_sup_left)
    omega
  have hne : (qOf T).relIndex (Bw T d x) ≠ 0 := by
    intro h0
    have h1 := Subgroup.relIndex_mul_card (H := qOf T) (K := Bw T d x)
    rw [h0, zero_mul] at h1
    exact (Nat.card_pos (α := ↥(Bw T d x))).ne' h1.symm
  have hrel : (qOf T).relIndex S ≤ 2 :=
    (Subgroup.relIndex_le_of_le_right hSB hne).trans hf.Bw_relIndex
  have hmul := Subgroup.relIndex_mul_card (H := qOf T) (K := S)
  rw [inf_comm] at hmul
  nlinarith

theorem card_le_four_of_pGroup (h : Ctx T M g A t d x) (hf : Wp0 T d x) (hZ : Z ≤ Gw d x)
    (hZn : ∀ u ∈ Gw d x, ∀ k ∈ Z, u * k * u⁻¹ ∈ Z) (hz : d * d ∉ Z) {S : Subgroup G}
    (hSZ : S ≤ Z) (hS2 : IsPGroup 2 S) : Nat.card S ≤ 4 := by
  obtain ⟨c, hc, hcS⟩ := exists_conj_le_sylow h.hSyl hS2 (hSZ.trans hZ)
  have hle : S.map (MulAut.conj c).toMonoidHom ≤ Tw T d x ⊓ Z := by
    rintro _ ⟨s, hs, rfl⟩
    exact ⟨hcS s hs, hZn c hc s (hSZ hs)⟩
  have hcard : Nat.card (S.map (MulAut.conj c).toMonoidHom) = Nat.card S :=
    Subgroup.card_map_of_injective (MulAut.conj c).injective
  rw [← hcard]
  exact card_le_four_of_le h hf (fun u hu k hk => hZn u hu.2 k hk) hz hle

end InspW2

end S143

end CFSG.Quasithin
