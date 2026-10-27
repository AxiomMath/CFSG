module

public import CFSG.RankThree.PartTwo.Sec21.FF84S34Ker
public import CFSG.RankThree.PartTwo.Sec21.FF84S34A8
public import CFSG.RankThree.PartTwo.Sec21.FF84A8
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_26ClaimTheta
public import CFSG.RankThree.PartTwo.Sec21.Hering2125CharTwo
public import CFSG.GH74.Exceptional.LinearFourTwo

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84

open CFSG CFSG.RankThree.PartTwo.Sec21 Equiv Equiv.Perm
open CFSG.LocalAnalysis.GLTheoremA.CatB (A8 a8P0 a8c a8d a8c8 a8d8 a8c8_mem_P0 a8d8_mem_P0 a8c8_val)

variable {G : Type} [Group G] [Finite G] {b b₁ b₂ : G} {L B : Subgroup G}

theorem zpow_eq_one_of_two_pow (hb : orderOf b = 3) {k : ℤ} {n : ℕ}
    (h : (b ^ k) ^ (2 ^ n) = 1) : b ^ k = 1 := by
  rw [← zpow_natCast, ← zpow_mul] at h
  have h1 : (3 : ℤ) ∣ k * 2 ^ n := by
    have := orderOf_dvd_iff_zpow_eq_one.2 h
    rw [hb] at this
    exact_mod_cast this
  have h3 : (3 : ℤ) ∣ k := by
    have hp : Prime (3 : ℤ) := Int.prime_three
    rcases hp.dvd_or_dvd h1 with h | h
    · exact h
    · exfalso
      have := hp.dvd_of_dvd_pow h
      omega
  exact orderOf_dvd_iff_zpow_eq_one.1 (by rw [hb]; exact_mod_cast h3)

theorem eq_one_or_eq_of_two_pow (hb : orderOf b = 3) {σ w : G} (hσ : σ * b = b * σ)
    (hσ2 : σ * σ = 1) (hw : w ∈ Subgroup.zpowers b ∨ w * σ⁻¹ ∈ Subgroup.zpowers b) {n : ℕ}
    (hn : w ^ (2 ^ n) = 1) : w = 1 ∨ w = σ := by
  rcases hw with hw | hw
  · left
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hw
    exact zpow_eq_one_of_two_pow hb hn
  · right
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hw
    have hwk : w = b ^ k * σ := by rw [hk]; group
    have hcomm : σ * b ^ k = b ^ k * σ := ((Commute.zpow_right (show Commute σ b from hσ) k)).eq
    have hww : w * w = (b ^ k) ^ 2 := by
      rw [hwk]
      calc b ^ k * σ * (b ^ k * σ) = b ^ k * (σ * b ^ k) * σ := by group
        _ = b ^ k * (b ^ k * σ) * σ := by rw [hcomm]
        _ = (b ^ k) ^ 2 * (σ * σ) := by group
        _ = (b ^ k) ^ 2 := by rw [hσ2, mul_one]
    have h2 : (b ^ k) ^ (2 ^ (n + 1)) = 1 := by
      have e1 : (b ^ k) ^ (2 ^ (n + 1)) = (w * w) ^ (2 ^ n) := by
        rw [hww, ← pow_mul, ← pow_succ']
      rw [e1, ← sq, ← pow_mul, mul_comm, pow_mul, hn, one_pow]
    have hk1 : b ^ k = 1 := zpow_eq_one_of_two_pow hb h2
    rw [hwk, hk1, one_mul]

structure ThetaData (b : G) (L Q : Subgroup G) where
  φ : ↥L ≃* alternatingGroup (Fin 8)
  θ : ↥(Cen b) →* Perm (Fin 8)
  hLC : L ≤ Cen b
  hLN : Cen b ≤ Nor L
  hQL : Q ≤ L
  spec : ∀ (c : ↥(Cen b)) (l l' : ↥L), (l' : G) = (c : G) * l * (c : G)⁻¹ →
    ((φ l' : alternatingGroup (Fin 8)) : Perm (Fin 8)) =
      θ c * ((φ l : alternatingGroup (Fin 8)) : Perm (Fin 8)) * (θ c)⁻¹
  ker : ∀ c : ↥(Cen b), θ c = 1 → ∀ k ∈ L, (c : G) * k = k * c
  onL : ∀ l : ↥L, θ ⟨l, hLC l.2⟩ = ((φ l : alternatingGroup (Fin 8)) : Perm (Fin 8))
  hP : ∀ z : ↥L, φ z ∈ a8P0 ↔ (z : G) ∈ Q

namespace ThetaData

variable {Q : Subgroup G} (T : ThetaData b L Q)

theorem comm_iff (c : ↥(Cen b)) (l : ↥L) :
    Commute (T.θ c) ((T.φ l : alternatingGroup (Fin 8)) : Perm (Fin 8)) ↔
      (c : G) * l = l * c := by
  have hmem : (c : G) * l * (c : G)⁻¹ ∈ L :=
    (Subgroup.mem_normalizer_iff.1 (T.hLN c.2) l).1 l.2
  have hs := T.spec c l ⟨_, hmem⟩ rfl
  constructor
  · intro h
    have h1 : ((T.φ ⟨_, hmem⟩ : alternatingGroup (Fin 8)) : Perm (Fin 8)) =
        ((T.φ l : alternatingGroup (Fin 8)) : Perm (Fin 8)) := by
      rw [hs, h.eq]; group
    have h2 : (⟨_, hmem⟩ : ↥L) = l := T.φ.injective (Subtype.ext h1)
    have h3 : (c : G) * l * (c : G)⁻¹ = l := congrArg Subtype.val h2
    calc (c : G) * l = (c : G) * l * (c : G)⁻¹ * c := by group
      _ = l * c := by rw [h3]
  · intro h
    have h3 : (c : G) * l * (c : G)⁻¹ = l := by
      calc (c : G) * l * (c : G)⁻¹ = l * c * (c : G)⁻¹ := by rw [h]
        _ = l := by group
    have h2 : (⟨_, hmem⟩ : ↥L) = l := Subtype.ext h3
    rw [h2] at hs
    show T.θ c * _ = _ * T.θ c
    calc T.θ c * ((T.φ l : alternatingGroup (Fin 8)) : Perm (Fin 8))
        = T.θ c * ((T.φ l : alternatingGroup (Fin 8)) : Perm (Fin 8)) * (T.θ c)⁻¹ * T.θ c := by
          group
      _ = ((T.φ l : alternatingGroup (Fin 8)) : Perm (Fin 8)) * T.θ c := by rw [← hs]

theorem mem_zpowers_of_one (hs : FF84Sec3 b L B b₁ b₂) (hO : Opp 3 (Cen b) = ⊥)
    (hZ : Subgroup.center L = ⊥) {c : ↥(Cen b)} (hc : T.θ c = 1) :
    (c : G) ∈ Subgroup.zpowers b :=
  mem_zpowers_of_cen_cen hs hO hZ c.2 (T.ker c hc)

theorem commute_P0 {c : ↥(Cen b)} (hc : ∀ z ∈ Q, (z : G) * c = c * z) {p : A8} (hp : p ∈ a8P0) :
    Commute (T.θ c) (p : Perm (Fin 8)) := by
  have hl := (T.hP (T.φ.symm p)).1 (by simpa using hp)
  have := (T.comm_iff c (T.φ.symm p)).2 (hc _ hl).symm
  simpa using this

end ThetaData

theorem closure_le_B (hs : FF84Sec3 b L B b₁ b₂) : Subgroup.closure ({b₁, b₂} : Set G) ≤ B := by
  rw [Subgroup.closure_le]
  intro z hz
  rcases hz with rfl | hz
  · exact mem_B_b₁ hs
  · rw [Set.mem_singleton_iff.1 hz]; exact mem_B_b₂ hs

theorem closure_le_L (hs : FF84Sec3 b L B b₁ b₂) : Subgroup.closure ({b₁, b₂} : Set G) ≤ L := by
  rw [← hs.gen]; exact inf_le_right

theorem exists_thetaData (hs : FF84Sec3 b L B b₁ b₂) (hZ : Subgroup.center L = ⊥) :
    Nonempty (ThetaData b L (Subgroup.closure ({b₁, b₂} : Set G))) := by
  obtain ⟨e⟩ : Nonempty (↥L ⧸ Subgroup.center ↥L ≃* alternatingGroup (Fin 8)) :=
    CFSG.GH74.Exceptional.nonempty_mulEquiv_alternating_eight_of_lieModel
      (Or.inl ⟨by decide, hs.hyp.model⟩)
  let φ0 : ↥L ≃* alternatingGroup (Fin 8) :=
    (QuotientGroup.quotientBot (G := ↥L)).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hZ.symm).trans e)
  have hb₁L : b₁ ∈ L := (Subgroup.mem_inf.1 hs.hb₁).2
  have hb₂L : b₂ ∈ L := (Subgroup.mem_inf.1 hs.hb₂).2
  set u : ↥L := ⟨b₁, hb₁L⟩ with hu
  set v : ↥L := ⟨b₂, hb₂L⟩ with hv
  have hu3 : u ^ 3 = 1 := Subtype.ext (pow3_of_mem_B hs (mem_B_b₁ hs))
  have hv3 : v ^ 3 = 1 := Subtype.ext (pow3_of_mem_B hs (mem_B_b₂ hs))
  have huv : u * v = v * u :=
    Subtype.ext (comm_of_mem_B hs (mem_B_b₁ hs) (mem_B_b₂ hs)).eq
  have hu1 : u ≠ 1 := fun h => b₁_ne_one hs (congrArg Subtype.val h)
  have hvu : v ∉ Subgroup.zpowers u := by
    intro hm
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hm
    exact b₂_notin_zpowers_b₁ hs (Subgroup.mem_zpowers_iff.2 ⟨k, by
      simpa using congrArg Subtype.val hk⟩)
  have hx3 : φ0 u ^ 3 = 1 := by rw [← map_pow, hu3, map_one]
  have hy3 : φ0 v ^ 3 = 1 := by rw [← map_pow, hv3, map_one]
  have hc : φ0 u * φ0 v = φ0 v * φ0 u := by rw [← map_mul, ← map_mul, huv]
  have hx1 : φ0 u ≠ 1 := fun h => hu1 (φ0.map_eq_one_iff.1 h)
  have hyx : φ0 v ∉ Subgroup.zpowers (φ0 u) := by
    intro hm
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hm
    apply hvu
    exact Subgroup.mem_zpowers_iff.2 ⟨k, φ0.injective (by rw [map_zpow]; exact hk)⟩
  have hPg : IsPGroup 3 (Subgroup.closure ({φ0 u, φ0 v} : Set A8)) := by
    refine CFSG.LocalAnalysis.GLTheoremA.CatB.isPGroup_closure_three _ ?_ ?_
    · intro s hs
      rcases hs with h | h
      · rw [h]; exact hx3
      · rw [Set.mem_singleton_iff] at h; rw [h]; exact hy3
    · intro s hs w hw
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs hw
      rcases hs with h | h <;> rcases hw with h' | h' <;> rw [h, h'] <;>
        first | rfl | exact hc | exact hc.symm
  obtain ⟨h, hh⟩ := exists_conj_into_P0 hPg
  let φ : ↥L ≃* alternatingGroup (Fin 8) := φ0.trans (MulAut.conj h)
  have hφ : ∀ z, φ z = h * φ0 z * h⁻¹ := fun z => by simp [φ, MulAut.conj_apply]
  have hxP : φ u ∈ a8P0 := by
    rw [hφ]; exact hh _ (Subgroup.subset_closure (by simp))
  have hyP : φ v ∈ a8P0 := by
    rw [hφ]; exact hh _ (Subgroup.subset_closure (by simp))
  have hx3' : φ u ^ 3 = 1 := by rw [← map_pow, hu3, map_one]
  have hx1' : φ u ≠ 1 := fun h => hu1 (φ.map_eq_one_iff.1 h)
  have hyx' : φ v ∉ Subgroup.zpowers (φ u) := by
    intro hm
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hm
    apply hvu
    exact Subgroup.mem_zpowers_iff.2 ⟨k, φ.injective (by rw [map_zpow]; exact hk)⟩
  have hcl := closure_pair_eq_P0 hxP hyP hx3' hx1' hyx'
  have h1 : Subgroup.closure ({φ u, φ v} : Set A8) =
      (Subgroup.closure ({u, v} : Set ↥L)).map φ.toMonoidHom := by
    rw [MonoidHom.map_closure, Set.image_pair]; rfl
  have h2 : Subgroup.closure ({b₁, b₂} : Set G) =
      (Subgroup.closure ({u, v} : Set ↥L)).map L.subtype := by
    rw [MonoidHom.map_closure, Set.image_pair]; rfl
  have hLN : Cen b ≤ Nor L := hs.hyp.hLN
  refine ⟨
    { φ := φ
      θ := (CFSG.QuasithinUnique.Claim2526.thetaHom L φ).comp (Subgroup.inclusion hLN)
      hLC := hs.hyp.hLC
      hLN := hLN
      hQL := closure_le_L hs
      spec := ?_
      ker := ?_
      onL := ?_
      hP := ?_ }⟩
  · intro c l l' hl
    have := CFSG.QuasithinUnique.Claim2526.theta_spec L φ ⟨c.1, hLN c.2⟩ l
    have e : L.normalizerMonoidHom ⟨c.1, hLN c.2⟩ l = l' := Subtype.ext (by rw [hl]; simp)
    rw [e] at this
    exact this
  · intro c hc
    exact (CFSG.QuasithinUnique.Claim2526.theta_eq_one_iff L φ ⟨c.1, hLN c.2⟩).1 hc
  · intro l
    exact CFSG.QuasithinUnique.Claim2526.theta_apply_of_mem L φ l
  · intro z
    have a1 : φ z ∈ (Subgroup.closure ({u, v} : Set ↥L)).map φ.toMonoidHom ↔
        z ∈ Subgroup.closure ({u, v} : Set ↥L) :=
      Subgroup.mem_map_iff_mem (f := φ.toMonoidHom) φ.injective
    have a2 : (z : G) ∈ (Subgroup.closure ({u, v} : Set ↥L)).map L.subtype ↔
        z ∈ Subgroup.closure ({u, v} : Set ↥L) :=
      Subgroup.mem_map_iff_mem (f := L.subtype) L.subtype_injective
    rw [← hcl, h1, h2]
    exact a1.trans a2.symm

theorem zpow_cube' {w : G} (hw : w ^ 3 = 1) (k : ℤ) : (w ^ k) ^ 3 = 1 := by
  rw [← zpow_natCast (w ^ k) 3, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hw, one_zpow]

theorem zpowers_inf_eq_bot (hs : FF84Sec3 b L B b₁ b₂) (hZ : Subgroup.center L = ⊥) :
    Subgroup.zpowers b ⊓ L = ⊥ := by
  rw [eq_bot_iff]
  rintro g ⟨hg1, hg2⟩
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg1
  have hcen : (⟨b ^ i, hg2⟩ : ↥L) ∈ Subgroup.center ↥L := by
    rw [Subgroup.mem_center_iff]
    intro k
    apply Subtype.ext
    show (k : G) * b ^ i = b ^ i * (k : G)
    exact ((Commute.zpow_right (show Commute (k : G) b from
      Subgroup.mem_centralizer_singleton_iff.1 (hs.hyp.hLC k.2)) i)).eq
  rw [hZ, Subgroup.mem_bot] at hcen
  exact Subgroup.mem_bot.2 (congrArg Subtype.val hcen)

theorem caseA (hs : FF84Sec3 b L B b₁ b₂) (hO : Opp 3 (Cen b) = ⊥) (hZ : Subgroup.center L = ⊥)
    (T : ThetaData b L (Subgroup.closure ({b₁, b₂} : Set G)))
    (hA : ∀ c : ↥(Cen b), sign (T.θ c) = 1) :
    Subgroup.zpowers b ⊔ L = Cen b ∧ CenS B = B := by
  have hLC : L ≤ Cen b := hs.hyp.hLC
  have hbC : b ∈ Cen b := Subgroup.mem_centralizer_singleton_iff.2 rfl
  have hsup : Cen b ≤ Subgroup.zpowers b ⊔ L := by
    intro c hc
    set c' : ↥(Cen b) := ⟨c, hc⟩ with hc'
    have hmem : T.θ c' ∈ alternatingGroup (Fin 8) := mem_alternatingGroup.2 (hA c')
    let l : ↥L := T.φ.symm ⟨T.θ c', hmem⟩
    have hl : T.θ ⟨l, T.hLC l.2⟩ = T.θ c' := by
      rw [T.onL]; simp [l]
    have hk : T.θ (c' * ⟨l, T.hLC l.2⟩⁻¹) = 1 := by
      rw [map_mul, map_inv, hl]; simp
    have h1 := T.mem_zpowers_of_one hs hO hZ hk
    have h2 : c * (l : G)⁻¹ ∈ Subgroup.zpowers b := by simpa [hc'] using h1
    have e : c = (c * (l : G)⁻¹) * l := by group
    rw [e]
    exact Subgroup.mul_mem_sup h2 l.2
  have hQB := closure_le_B hs
  have hCB : CenS B = B := by
    apply le_antisymm
    · intro c hc
      have hcb : c ∈ Cen b := Subgroup.mem_centralizer_singleton_iff.2
        (Subgroup.mem_centralizer_iff.1 hc b (mem_B_b hs)).symm
      obtain ⟨i, l, hl, hcl⟩ := exists_zpow_mul_of_mem_sup_cen hLC (hsup hcb)
      have hlc : ∀ z ∈ Subgroup.closure ({b₁, b₂} : Set G), z * l = l * z := by
        intro z hz
        have hzB : z ∈ B := hQB hz
        have h1 : z * c = c * z := Subgroup.mem_centralizer_iff.1 hc z hzB
        have h2 : z * b ^ i = b ^ i * z :=
          ((comm_of_mem_B hs hzB (mem_B_b hs)).zpow_right i).eq
        have hl' : l = (b ^ i)⁻¹ * c := by rw [hcl]; group
        rw [hl']
        have h3 : z * (b ^ i)⁻¹ = (b ^ i)⁻¹ * z := ((Commute.inv_right (show Commute z (b ^ i) from h2))).eq
        calc z * ((b ^ i)⁻¹ * c) = (z * (b ^ i)⁻¹) * c := by group
          _ = (b ^ i)⁻¹ * (z * c) := by rw [h3]; group
          _ = (b ^ i)⁻¹ * (c * z) := by rw [h1]
          _ = ((b ^ i)⁻¹ * c) * z := by group
      let l' : ↥L := ⟨l, hl⟩
      have hcomm : ∀ {p : A8}, p ∈ a8P0 → Commute ((T.φ l' : alternatingGroup (Fin 8)) :
          Perm (Fin 8)) (p : Perm (Fin 8)) := by
        intro p hp
        have := T.commute_P0 (c := ⟨l, hLC hl⟩) (fun z hz => hlc z hz) hp
        rwa [show T.θ ⟨l, hLC hl⟩ = _ from T.onL l'] at this
      have hP : T.φ l' ∈ a8P0 :=
        mem_P0_of_comm (hcomm a8c8_mem_P0).eq (hcomm a8d8_mem_P0).eq
      have hlQ : l ∈ Subgroup.closure ({b₁, b₂} : Set G) := (T.hP l').1 hP
      rw [hcl]
      exact mul_mem (Subgroup.zpow_mem _ (mem_B_b hs) i) (hQB hlQ)
    · intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact (comm_of_mem_B hs hy hx).eq
  exact ⟨le_antisymm (sup_le (Subgroup.zpowers_le.2 hbC) hLC) hsup, hCB⟩

theorem caseB (hs : FF84Sec3 b L B b₁ b₂) (hO : Opp 3 (Cen b) = ⊥) (hZ : Subgroup.center L = ⊥)
    (T : ThetaData b L (Subgroup.closure ({b₁, b₂} : Set G)))
    (hgen : ∀ U : Subgroup G, IsPGroup 2 U → B ≤ Nor U →
      (U ⊓ Cen b₁) ⊔ (U ⊓ Cen b₂) ⊔ (U ⊓ Cen b) = U)
    {c0 : ↥(Cen b)} (hc0 : sign (T.θ c0) = -1) : False := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hb : orderOf b = 3 := hs.hyp.ord
  have hb3 : b ^ 3 = 1 := hb ▸ pow_orderOf_eq_one b
  have hbC : b ∈ Cen b := Subgroup.mem_centralizer_singleton_iff.2 rfl
  have hker : ∀ c : ↥(Cen b), T.θ c = 1 → (c : G) ∈ Subgroup.zpowers b :=
    fun c hc => T.mem_zpowers_of_one hs hO hZ hc
  have hQB := closure_le_B hs
  have hcomm_a8c : ∀ c : ↥(Cen b), (c : G) ∈ CenS B → T.θ c * a8c = a8c * T.θ c := fun c hc =>
    (T.commute_P0 (fun z hz => Subgroup.mem_centralizer_iff.1 hc z (hQB hz)) a8c8_mem_P0).eq
  have hcomm_a8d : ∀ c : ↥(Cen b), (c : G) ∈ CenS B → T.θ c * a8d = a8d * T.θ c := fun c hc =>
    (T.commute_P0 (fun z hz => Subgroup.mem_centralizer_iff.1 hc z (hQB hz)) a8d8_mem_P0).eq
  set w : Perm (Fin 8) := a8t * (T.θ c0)⁻¹ with hw
  have hwsign : sign w = 1 := by
    rw [hw, Perm.sign_mul, sign_inv, hc0, sign_a8t]; simp
  let l0 : ↥L := T.φ.symm ⟨w, mem_alternatingGroup.2 hwsign⟩
  have hl0 : ((T.φ l0 : alternatingGroup (Fin 8)) : Perm (Fin 8)) = w := by simp [l0]
  let c' : ↥(Cen b) := ⟨l0, T.hLC l0.2⟩ * c0
  have hθc' : T.θ c' = a8t := by
    rw [map_mul, T.onL, hl0, hw]; group
  have hcQ : ∀ z ∈ Subgroup.closure ({b₁, b₂} : Set G), (c' : G) * z = z * c' := by
    intro z hz
    have hzL : z ∈ L := T.hQL hz
    refine (T.comm_iff c' ⟨z, hzL⟩).1 ?_
    rw [hθc']
    exact (comm_a8t_of_mem_P0 ((T.hP ⟨z, hzL⟩).2 hz)).symm
  have hc'B : (c' : G) ∈ CenS B := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hBc : B ≤ Cen (c' : G) := by
      apply B_le_of_mem hs
      · exact Subgroup.mem_centralizer_singleton_iff.2
          (Subgroup.mem_centralizer_singleton_iff.1 c'.2).symm
      · exact Subgroup.mem_centralizer_singleton_iff.2
          (hcQ b₁ (Subgroup.subset_closure (by simp))).symm
      · exact Subgroup.mem_centralizer_singleton_iff.2
          (hcQ b₂ (Subgroup.subset_closure (by simp))).symm
    exact Subgroup.mem_centralizer_singleton_iff.1 (hBc hx)
  let σ' : ↥(Cen b) := c' ^ 3
  set σ : G := (σ' : G) with hσ
  have ha8t3 : a8t ^ 3 = a8t := by
    calc a8t ^ 3 = (a8t * a8t) * a8t := by rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ, pow_two]
      _ = a8t := by rw [a8t_sq, one_mul]
  have hθσ : T.θ σ' = a8t := by
    simp only [σ', map_pow, hθc']; exact ha8t3
  have hc'2 : (c' : G) ^ 2 ∈ Subgroup.zpowers b := by
    have h1 : T.θ (c' ^ 2) = 1 := by rw [map_pow, hθc', pow_two, a8t_sq]
    simpa using hker _ h1
  have hσ2 : σ * σ = 1 := by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hc'2
    have h1 : σ * σ = ((c' : G) ^ 2) ^ 3 := by
      show (c' : G) ^ 3 * (c' : G) ^ 3 = _
      group
    rw [h1, ← hk]
    exact zpow_cube' hb3 k
  have hσ1 : σ ≠ 1 := by
    intro h
    have h1 : σ' = 1 := Subtype.ext h
    rw [h1, map_one] at hθσ
    exact a8t_ne_one hθσ.symm
  have hσC : σ ∈ Cen b := σ'.2
  have hσB : σ ∈ CenS B := pow_mem hc'B 3
  have hσb : σ * b = b * σ := Subgroup.mem_centralizer_singleton_iff.1 hσC
  have huniq : ∀ n ∈ Nor B, n * σ * n⁻¹ = σ := by
    intro n hn
    set u : G := n * σ * n⁻¹ with hu
    have hBn : ∀ x ∈ B, n⁻¹ * x * n ∈ B := by
      intro x hx
      have := (Subgroup.mem_normalizer_iff.1 (inv_mem hn) x).1 hx
      simpa using this
    have huC : u ∈ CenS B := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have hc := Subgroup.mem_centralizer_iff.1 hσB (n⁻¹ * x * n) (hBn x hx)
      calc x * u = n * ((n⁻¹ * x * n) * σ) * n⁻¹ := by rw [hu]; group
        _ = n * (σ * (n⁻¹ * x * n)) * n⁻¹ := by rw [hc]
        _ = u * x := by rw [hu]; group
    have huCb : u ∈ Cen b := Subgroup.mem_centralizer_singleton_iff.2
      (Subgroup.mem_centralizer_iff.1 huC b (mem_B_b hs)).symm
    have hu2 : u * u = 1 := by
      calc u * u = n * (σ * σ) * n⁻¹ := by rw [hu]; group
        _ = 1 := by rw [hσ2]; group
    let u' : ↥(Cen b) := ⟨u, huCb⟩
    have hθu2 : T.θ u' * T.θ u' = 1 := by
      rw [← map_mul]
      have : u' * u' = 1 := Subtype.ext hu2
      rw [this, map_one]
    have hθu : T.θ u' = 1 ∨ T.θ u' = a8t :=
      eq_one_or_eq_a8t_of_comm (hcomm_a8c u' huC) (hcomm_a8d u' huC) hθu2
    have hcase : u ∈ Subgroup.zpowers b ∨ u * σ⁻¹ ∈ Subgroup.zpowers b := by
      rcases hθu with h | h
      · exact Or.inl (hker u' h)
      · right
        have h1 : T.θ (u' * σ'⁻¹) = 1 := by rw [map_mul, map_inv, h, hθσ]; group
        simpa using hker _ h1
    have h1 := eq_one_or_eq_of_two_pow hb hσb hσ2 hcase (n := 1)
      (by rw [pow_one, pow_two]; exact hu2)
    rcases h1 with h1 | h1
    · exfalso; apply hσ1
      calc σ = n⁻¹ * u * n := by rw [hu]; group
        _ = 1 := by rw [h1]; group
    · exact h1
  set U : Subgroup G := Op 2 (Cen σ) with hU
  have hU2 : IsPGroup 2 U := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (Cen σ)
  have hUn : Cen σ ≤ Nor U := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (Cen σ)
  have hBU : B ≤ Nor U := fun x hx => hUn (Subgroup.mem_centralizer_singleton_iff.2
    (Subgroup.mem_centralizer_iff.1 hσB x hx))
  have hUb : U ⊓ Cen b ≤ Subgroup.zpowers σ := by
    intro w hw
    obtain ⟨hwU, hwb⟩ := Subgroup.mem_inf.1 hw
    have hwσ : w ∈ Cen σ := CFSG.LieType.BorelTits.pCoreOf_le 2 (Cen σ) hwU
    obtain ⟨n, hn⟩ := hU2 ⟨w, hwU⟩
    have hwn : w ^ (2 ^ n) = 1 := by
      have := congrArg Subtype.val hn
      simpa using this
    let w' : ↥(Cen b) := ⟨w, hwb⟩
    have hθw : T.θ w' = 1 ∨ T.θ w' = a8t := by
      by_contra hne
      push Not at hne
      have hcomm : T.θ w' * a8t = a8t * T.θ w' := by
        rw [← hθσ, ← map_mul, ← map_mul]
        congr 1
        exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 hwσ)
      have hx8 : T.θ w' ^ 8 = 1 := pow8_of_two_pow _ (n := n) (by
        rw [← map_pow]
        have : w' ^ (2 ^ n) = 1 := Subtype.ext hwn
        rw [this, map_one])
      obtain ⟨y, -, hysign, hyt, hne2⟩ :=
        exists_two_elt_product (T.θ w') hcomm hx8 hne.1 hne.2
      let l : ↥L := T.φ.symm ⟨y, mem_alternatingGroup.2 hysign⟩
      have hl : ((T.φ l : alternatingGroup (Fin 8)) : Perm (Fin 8)) = y := by simp [l]
      let lC : ↥(Cen b) := ⟨l, T.hLC l.2⟩
      have hθl : T.θ lC = y := by
        show T.θ ⟨l, T.hLC l.2⟩ = y
        rw [T.onL, hl]
      have hlσ : (σ' : G) * l = l * σ' := by
        refine (T.comm_iff σ' l).1 ?_
        rw [hθσ, hl]
        exact hyt.symm
      have hlCσ : (l : G) ∈ Cen σ := Subgroup.mem_centralizer_singleton_iff.2 hlσ.symm
      have hlU : ∀ x ∈ U, (l : G) * x * (l : G)⁻¹ ∈ U := fun x hx =>
        (Subgroup.mem_normalizer_iff.1 (hUn hlCσ) x).1 hx
      have hw2 : w * ((l : G) * w * (l : G)⁻¹) ∈ U := mul_mem hwU (hlU w hwU)
      have hw2b : w * ((l : G) * w * (l : G)⁻¹) ∈ Cen b :=
        mul_mem hwb (mul_mem (mul_mem lC.2 hwb) (inv_mem lC.2))
      obtain ⟨m, hm⟩ := hU2 ⟨_, hw2⟩
      have hm' : (⟨_, hw2b⟩ : ↥(Cen b)) ^ (2 ^ m) = 1 := by
        have := congrArg Subtype.val hm
        exact Subtype.ext (by simpa using this)
      have hθ : T.θ ⟨_, hw2b⟩ = T.θ w' * (y * T.θ w' * y⁻¹) := by
        have : (⟨_, hw2b⟩ : ↥(Cen b)) = w' * (lC * w' * lC⁻¹) := rfl
        rw [this, map_mul, map_mul, map_mul, map_inv, hθl]
      have h8 := pow8_of_two_pow (T.θ ⟨_, hw2b⟩) (n := m) (by rw [← map_pow, hm', map_one])
      rw [hθ] at h8
      exact hne2 h8
    have hcase : w ∈ Subgroup.zpowers b ∨ w * σ⁻¹ ∈ Subgroup.zpowers b := by
      rcases hθw with h | h
      · exact Or.inl (hker w' h)
      · right
        have h1 : T.θ (w' * σ'⁻¹) = 1 := by rw [map_mul, map_inv, h, hθσ]; group
        simpa using hker _ h1
    rcases eq_one_or_eq_of_two_pow hb hσb hσ2 hcase hwn with h | h
    · rw [h]; exact one_mem _
    · rw [h]; exact Subgroup.mem_zpowers σ
  have hUi : ∀ (bi n : G), n ∈ Nor B → n * b * n⁻¹ = bi → U ⊓ Cen bi ≤ Subgroup.zpowers σ := by
    intro bi n hn hnb w hw
    obtain ⟨hwU, hwbi⟩ := Subgroup.mem_inf.1 hw
    have hnσ : n * σ = σ * n := mul_inv_eq_iff_eq_mul.1 (huniq n hn)
    have hnC : n⁻¹ ∈ Cen σ := by
      refine Subgroup.mem_centralizer_singleton_iff.2 ?_
      calc n⁻¹ * σ = n⁻¹ * (σ * n) * n⁻¹ := by group
        _ = n⁻¹ * (n * σ) * n⁻¹ := by rw [hnσ]
        _ = σ * n⁻¹ := by group
    have hn'U : n⁻¹ * w * n ∈ U := by
      have := (Subgroup.mem_normalizer_iff.1 (hUn hnC) w).1 hwU
      simpa using this
    have hwcomm : w * bi = bi * w := Subgroup.mem_centralizer_singleton_iff.1 hwbi
    have hn'b : n⁻¹ * w * n ∈ Cen b := by
      refine Subgroup.mem_centralizer_singleton_iff.2 ?_
      calc (n⁻¹ * w * n) * b = n⁻¹ * w * (n * b * n⁻¹) * n := by group
        _ = n⁻¹ * (w * bi) * n := by rw [hnb]; group
        _ = n⁻¹ * (bi * w) * n := by rw [hwcomm]
        _ = b * (n⁻¹ * w * n) := by rw [← hnb]; group
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hUb ⟨hn'U, hn'b⟩)
    have hcσ : Commute n σ := hnσ
    have : w = σ ^ k := by
      calc w = n * (n⁻¹ * w * n) * n⁻¹ := by group
        _ = n * σ ^ k * n⁻¹ := by rw [hk]
        _ = σ ^ k := by rw [(hcσ.zpow_right k).eq]; group
    rw [this]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers σ) k
  obtain ⟨-, -, -, -, -, ⟨n3, hn3, e3b, e3b1, -⟩⟩ := hs.mono
  have hU1 : U ⊓ Cen b₁ ≤ Subgroup.zpowers σ := hUi b₁ n3 hn3 e3b
  have hU2' : U ⊓ Cen b₂ ≤ Subgroup.zpowers σ := hUi b₂ (n3 * n3) (mul_mem hn3 hn3) (by
    calc n3 * n3 * b * (n3 * n3)⁻¹ = n3 * (n3 * b * n3⁻¹) * n3⁻¹ := by group
      _ = b₂ := by rw [e3b, e3b1])
  have hUle : U ≤ Subgroup.zpowers σ :=
    (hgen U hU2 hBU).symm.le.trans (sup_le (sup_le hU1 hU2') hUb)
  have hzσ2 : IsPGroup 2 (Subgroup.zpowers σ) :=
    IsPGroup.of_card (n := 1) (by
      rw [Nat.card_zpowers, pow_one, orderOf_eq_prime (by rw [pow_two]; exact hσ2) hσ1])
  have hzne : Subgroup.zpowers σ ≠ ⊥ := by
    intro h
    exact hσ1 (Subgroup.zpowers_eq_bot.1 h)
  have hbcen : b ∈ Subgroup.centralizer ((Subgroup.zpowers σ : Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
    exact ((Commute.zpow_left (show Commute σ b from hσb) k)).eq
  obtain ⟨x, hx, hxne⟩ := Hering2125.exists_moved_of_charTwo hs.hyp.char2 hzσ2 hzne hbcen hb3
    (b_ne_one' hs)
  have hcen : Subgroup.centralizer ((Subgroup.zpowers σ : Subgroup G) : Set G) = Cen σ := by
    ext y
    rw [Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h; exact (h σ (Subgroup.mem_zpowers σ)).symm
    · intro h z hz
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
      exact ((Commute.zpow_left (show Commute σ y from h.symm) k)).eq
  rw [hcen] at hx
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 (hUle hx)
  apply hxne
  have hc : Commute b (σ ^ k) := Commute.zpow_right (show Commute b σ from hσb.symm) k
  rw [hc.eq]; group

theorem ff84_3_4_of (h31 : FF84_3_1) (h33 : FF84_3_3) : FF84_3_4 := by
  intro G _ _ b L B b₁ b₂ hs
  obtain ⟨hO, hZ⟩ := h31 G b L B b₁ b₂ hs
  obtain ⟨T⟩ := exists_thetaData hs hZ
  by_cases hA : ∀ c : ↥(Cen b), sign (T.θ c) = 1
  · obtain ⟨h1, h2⟩ := caseA hs hO hZ T hA
    exact ⟨h1, zpowers_inf_eq_bot hs hZ, h2⟩
  · exfalso
    push Not at hA
    obtain ⟨c0, hc0⟩ := hA
    have hc0' : sign (T.θ c0) = -1 := by
      rcases Int.units_eq_one_or (sign (T.θ c0)) with h | h
      · exact absurd h hc0
      · exact h
    exact caseB hs hO hZ T (fun U hU hBU => (h33 G b L B b₁ b₂ hs).2.2 U hU hBU) hc0'

end CFSG.RankThree.PartTwo.Sec21.FF84
