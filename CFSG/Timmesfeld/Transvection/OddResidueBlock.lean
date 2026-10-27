module

public import CFSG.Timmesfeld.Transvection.OddCPart
public import CFSG.Timmesfeld.Transvection.OddSU3Chord
import CFSG.Timmesfeld.Transvection.OddSU3Aut
import CFSG.Timmesfeld.Transvection.OddResidueLiftConj
public import CFSG.Timmesfeld.Transvection.FrameResidue

public section

namespace CFSG.Timmesfeld.Transvection

open CFSG.Timmesfeld.ARS CFSG.LieType.Universal.Unitary CFSG.LieType.Steinberg
open CFSG.LocalAnalysis.UniquenessCase CFSG.LieType.CurtisTits CFSG.LieType.BorelTits
open CFSG.Timmesfeld.Transvection.Pres

variable {H : Type} [Group H] {Δ : Set (Subgroup H)} {r : ℕ} {P Q : Fin r → Subgroup H}
  {k : Fin r} {F : Type} [Field F] [Finite F] [CharP F 2] {n : ℕ}


theorem SURelations.HasFrameImages.map_lastBlock {m : ℕ}
    (hFn : Nat.card F = (2 ^ n) ^ 2) (he : Even m) (hm : 4 ≤ m)
    {P Q : Fin (m / 2) → Subgroup H}
    {R : SURelations (m / 2) (unitaryInvolution F 2 n) H}
    (hR : R.HasFrameImages Δ P Q) :
    (su2Top (unitaryInvolution F 2 n)).map (R.lastBlock hFn he hm) =
        P ⟨m / 2 - 1, Nat.sub_lt (Nat.div_pos (Nat.le_trans (Nat.le_add_right 2 2) hm)
          Nat.two_pos) Nat.zero_lt_one⟩ ∧
      (su2Bot (unitaryInvolution F 2 n)).map (R.lastBlock hFn he hm) =
        Q ⟨m / 2 - 1, Nat.sub_lt (Nat.div_pos (Nat.le_trans (Nat.le_add_right 2 2) hm)
          Nat.two_pos) Nat.zero_lt_one⟩ := by
  let k : Fin (m / 2) := ⟨m / 2 - 1, by omega⟩
  constructor
  · apply le_antisymm
    · rintro - ⟨x, hx, rfl⟩
      obtain ⟨c, hc, rfl⟩ := (mem_su2Top_iff (σ := unitaryInvolution F 2 n)).1 hx
      exact (hR.long (Sum.inl k) _).2 ⟨c, hc, (R.lastBlock_suLong_inl hFn he hm hc).symm⟩
    · intro y hy
      obtain ⟨c, hc, rfl⟩ := (hR.long (Sum.inl k) y).1 (by simpa [framePt] using hy)
      exact ⟨suLong (unitaryInvolution F 2 n) (Sum.inl 0) c,
        (mem_su2Top_iff (σ := unitaryInvolution F 2 n)).2 ⟨c, hc, rfl⟩,
        R.lastBlock_suLong_inl hFn he hm hc⟩
  · apply le_antisymm
    · rintro - ⟨x, hx, rfl⟩
      obtain ⟨c, hc, rfl⟩ := (mem_su2Bot_iff (σ := unitaryInvolution F 2 n)).1 hx
      exact (hR.long (Sum.inr k) _).2 ⟨c, hc, (R.lastBlock_suLong_inr hFn he hm hc).symm⟩
    · intro y hy
      obtain ⟨c, hc, rfl⟩ := (hR.long (Sum.inr k) y).1 (by simpa [framePt] using hy)
      exact ⟨suLong (unitaryInvolution F 2 n) (Sum.inr 0) c,
        (mem_su2Bot_iff (σ := unitaryInvolution F 2 n)).2 ⟨c, hc, rfl⟩,
        R.lastBlock_suLong_inr hFn he hm hc⟩

private theorem map_comp_symm_eq_of_map_eq {G K : Type*} [Group G] [Group K]
    {e₁ e₂ : G ≃* K} {S : Subgroup G}
    (h : S.map e₁.toMonoidHom = S.map e₂.toMonoidHom) :
    S.map (e₂.symm.toMonoidHom.comp e₁.toMonoidHom) = S := by
  have hcomp : e₂.symm.toMonoidHom.comp e₂.toMonoidHom = MonoidHom.id G := by
    ext x
    simp
  rw [← Subgroup.map_map, h, Subgroup.map_map, hcomp, Subgroup.map_id]

section AllCertificates


private theorem card_SU2_sup [Finite H] (hΔ : IsRootClass Δ) (hF : IsMaxFrame Δ P Q)
    (hq : ∀ A ∈ Δ, 4 ≤ Nat.card A) (hcard : ∀ A ∈ Δ, Nat.card A = 2 ^ n)
    (hFn : Nat.card F = (2 ^ n) ^ 2) :
    Nat.card (SU (unitaryInvolution F 2 n) 2) = 2 ^ n * ((2 ^ n) ^ 2 - 1) ∧
      Nat.card ↥(P k ⊔ Q k) = 2 ^ n * ((2 ^ n) ^ 2 - 1) := by
  have hnpos : 0 < n := by
    have h4 : 4 ≤ 2 ^ n := by
      rw [← hcard (P k) (hF.memP k)]
      exact hq (P k) (hF.memP k)
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · rw [h0, pow_zero] at h4
      omega
    · exact hpos
  constructor
  · simpa using card_SU_two (p := 2) (f := n) hFn
  · have hPcard : Nat.card (P k) = 2 ^ n := hcard (P k) (hF.memP k)
    obtain ⟨m, -, hPm, e, -⟩ :=
      Opposite.exists_mulEquiv_SL2 hΔ (hF.memP k) (hF.opposite k)
        (hq (P k) (hF.memP k))
    have hmn : m = n := Nat.pow_right_injective le_rfl (hPm.symm.trans hPcard)
    rw [hmn] at e
    rw [Nat.card_congr e.toEquiv, card_specialLinearGroup_fin_two (GaloisField 2 n),
      GaloisField.card 2 n hnpos.ne']

private theorem map_equiv_of_val_eq {G : Type*} [Group G]
    {S : Subgroup G} {f : G →* H} {e : G ≃* ↥(P k ⊔ Q k)}
    (hval : ∀ x, (e.toMonoidHom x : H) = f x) :
    S.map e.toMonoidHom = (S.map f).subgroupOf (P k ⊔ Q k) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    change (e.toMonoidHom x : H) ∈ S.map f
    rw [hval x]
    exact Subgroup.mem_map_of_mem f hx
  · intro hy
    change (y : H) ∈ S.map f at hy
    obtain ⟨x, hx, hxy⟩ := hy
    refine ⟨x, hx, Subtype.ext ?_⟩
    change (e.toMonoidHom x : H) = (y : H)
    rw [hval x, hxy]

private theorem exists_SU2_equivs [Finite H] (hΔ : IsRootClass Δ) (hF : IsMaxFrame Δ P Q)
    (hq : ∀ A ∈ Δ, 4 ≤ Nat.card A) (hcard : ∀ A ∈ Δ, Nat.card A = 2 ^ n)
    (hFn : Nat.card F = (2 ^ n) ^ 2)
    (ψ : SU (unitaryInvolution F 2 n) 2 →* H)
    (ht : (su2Top (unitaryInvolution F 2 n)).map ψ = P k)
    (hb : (su2Bot (unitaryInvolution F 2 n)).map ψ = Q k)
    {θ₂ : SU (unitaryInvolution F 2 n) 3 →* H}
    (hθ₂top : (su3Top (unitaryInvolution F 2 n)).map θ₂ = P k)
    (hθ₂bot : (su3Bot (unitaryInvolution F 2 n)).map θ₂ = Q k) :
    ∃ ψe φe : SU (unitaryInvolution F 2 n) 2 ≃* ↥(P k ⊔ Q k),
      (∀ x, (ψe.toMonoidHom x : H) = ψ x) ∧
        ∀ x, (φe.toMonoidHom x : H) = (θ₂.comp (su3Chord (unitaryInvolution F 2 n))) x := by
  classical
  let φ : SU (unitaryInvolution F 2 n) 2 →* H :=
    θ₂.comp (su3Chord (unitaryInvolution F 2 n))
  have hφtop : (su2Top (unitaryInvolution F 2 n)).map φ = P k := by
    change (su2Top (unitaryInvolution F 2 n)).map
      (θ₂.comp (su3Chord (unitaryInvolution F 2 n))) = P k
    rw [← Subgroup.map_map, map_su2Top_su3Chord, hθ₂top]
  have hφbot : (su2Bot (unitaryInvolution F 2 n)).map φ = Q k := by
    change (su2Bot (unitaryInvolution F 2 n)).map
      (θ₂.comp (su3Chord (unitaryInvolution F 2 n))) = Q k
    rw [← Subgroup.map_map, map_su2Bot_su3Chord, hθ₂bot]
  have hψrange : ψ.range = P k ⊔ Q k := by
    rw [MonoidHom.range_eq_map, ← su2Top_sup_su2Bot hFn, Subgroup.map_sup, ht, hb]
  have hφrange : φ.range = P k ⊔ Q k := by
    rw [MonoidHom.range_eq_map, ← su2Top_sup_su2Bot hFn, Subgroup.map_sup, hφtop, hφbot]
  have hcards := card_SU2_sup (F := F) (n := n) (k := k) hΔ hF hq hcard hFn
  have hψmem : ∀ x, ψ x ∈ P k ⊔ Q k := fun x => by
    rw [← hψrange]
    exact MonoidHom.mem_range.mpr ⟨x, rfl⟩
  have hφmem : ∀ x, φ x ∈ P k ⊔ Q k := fun x => by
    rw [← hφrange]
    exact MonoidHom.mem_range.mpr ⟨x, rfl⟩
  let ψ' : SU (unitaryInvolution F 2 n) 2 →* ↥(P k ⊔ Q k) :=
    ψ.codRestrict (P k ⊔ Q k) hψmem
  let φ' : SU (unitaryInvolution F 2 n) 2 →* ↥(P k ⊔ Q k) :=
    φ.codRestrict (P k ⊔ Q k) hφmem
  have hψ'surj : Function.Surjective ψ' := by
    intro y
    have hy : (y : H) ∈ ψ.range := by rw [hψrange]; exact y.2
    obtain ⟨x, hx⟩ := MonoidHom.mem_range.mp hy
    exact ⟨x, Subtype.ext hx⟩
  have hφ'surj : Function.Surjective φ' := by
    intro y
    have hy : (y : H) ∈ φ.range := by rw [hφrange]; exact y.2
    obtain ⟨x, hx⟩ := MonoidHom.mem_range.mp hy
    exact ⟨x, Subtype.ext hx⟩
  let ψe : SU (unitaryInvolution F 2 n) 2 ≃* ↥(P k ⊔ Q k) :=
    MulEquiv.ofBijective ψ' (hψ'surj.bijective_of_nat_card_le
      (by rw [hcards.1, hcards.2]))
  let φe : SU (unitaryInvolution F 2 n) 2 ≃* ↥(P k ⊔ Q k) :=
    MulEquiv.ofBijective φ' (hφ'surj.bijective_of_nat_card_le
      (by rw [hcards.1, hcards.2]))
  exact ⟨ψe, φe, fun x => rfl, fun x => rfl⟩

private theorem map_SU2_equivs
    {ψ : SU (unitaryInvolution F 2 n) 2 →* H}
    (ht : (su2Top (unitaryInvolution F 2 n)).map ψ = P k)
    (hb : (su2Bot (unitaryInvolution F 2 n)).map ψ = Q k)
    {θ₂ : SU (unitaryInvolution F 2 n) 3 →* H}
    (hθ₂top : (su3Top (unitaryInvolution F 2 n)).map θ₂ = P k)
    (hθ₂bot : (su3Bot (unitaryInvolution F 2 n)).map θ₂ = Q k)
    {ψe φe : SU (unitaryInvolution F 2 n) 2 ≃* ↥(P k ⊔ Q k)}
    (hψval : ∀ x, (ψe.toMonoidHom x : H) = ψ x)
    (hφval : ∀ x, (φe.toMonoidHom x : H) = (θ₂.comp (su3Chord (unitaryInvolution F 2 n))) x) :
    (su2Top (unitaryInvolution F 2 n)).map ψe.toMonoidHom =
        (P k).subgroupOf (P k ⊔ Q k) ∧
      (su2Bot (unitaryInvolution F 2 n)).map ψe.toMonoidHom =
        (Q k).subgroupOf (P k ⊔ Q k) ∧
      (su2Top (unitaryInvolution F 2 n)).map φe.toMonoidHom =
        (P k).subgroupOf (P k ⊔ Q k) ∧
      (su2Bot (unitaryInvolution F 2 n)).map φe.toMonoidHom =
        (Q k).subgroupOf (P k ⊔ Q k) := by
  have hφtop : (su2Top (unitaryInvolution F 2 n)).map
      (θ₂.comp (su3Chord (unitaryInvolution F 2 n))) = P k := by
    change (su2Top (unitaryInvolution F 2 n)).map
      (θ₂.comp (su3Chord (unitaryInvolution F 2 n))) = P k
    rw [← Subgroup.map_map, map_su2Top_su3Chord, hθ₂top]
  have hφbot : (su2Bot (unitaryInvolution F 2 n)).map
      (θ₂.comp (su3Chord (unitaryInvolution F 2 n))) = Q k := by
    change (su2Bot (unitaryInvolution F 2 n)).map
      (θ₂.comp (su3Chord (unitaryInvolution F 2 n))) = Q k
    rw [← Subgroup.map_map, map_su2Bot_su3Chord, hθ₂bot]
  have hψtop := map_equiv_of_val_eq
    (S := su2Top (unitaryInvolution F 2 n)) (f := ψ) (e := ψe)
    hψval
  have hψbot := map_equiv_of_val_eq
    (S := su2Bot (unitaryInvolution F 2 n)) (f := ψ) (e := ψe)
    hψval
  have hφ'top := map_equiv_of_val_eq
    (S := su2Top (unitaryInvolution F 2 n))
    (f := θ₂.comp (su3Chord (unitaryInvolution F 2 n))) (e := φe)
    hφval
  have hφ'bot := map_equiv_of_val_eq
    (S := su2Bot (unitaryInvolution F 2 n))
    (f := θ₂.comp (su3Chord (unitaryInvolution F 2 n))) (e := φe)
    hφval
  rw [ht] at hψtop
  rw [hb] at hψbot
  rw [hφtop] at hφ'top
  rw [hφbot] at hφ'bot
  exact ⟨hψtop, hψbot, hφ'top, hφ'bot⟩

private theorem exists_block_alpha
    (ψ : SU (unitaryInvolution F 2 n) 2 →* H)
    {θ₂ : SU (unitaryInvolution F 2 n) 3 →* H}
    {ψe φe : SU (unitaryInvolution F 2 n) 2 ≃* ↥(P k ⊔ Q k)}
    (hψtop : (su2Top (unitaryInvolution F 2 n)).map ψe.toMonoidHom =
      (P k).subgroupOf (P k ⊔ Q k))
    (hψbot : (su2Bot (unitaryInvolution F 2 n)).map ψe.toMonoidHom =
      (Q k).subgroupOf (P k ⊔ Q k))
    (hφtop : (su2Top (unitaryInvolution F 2 n)).map φe.toMonoidHom =
      (P k).subgroupOf (P k ⊔ Q k))
    (hφbot : (su2Bot (unitaryInvolution F 2 n)).map φe.toMonoidHom =
      (Q k).subgroupOf (P k ⊔ Q k))
    (hψval : ∀ x, (ψe.toMonoidHom x : H) = ψ x)
    (hφval : ∀ x, (φe.toMonoidHom x : H) = (θ₂.comp (su3Chord (unitaryInvolution F 2 n))) x) :
    ∃ α : MulAut (SU (unitaryInvolution F 2 n) 2),
      (su2Top (unitaryInvolution F 2 n)).map α.toMonoidHom =
          su2Top (unitaryInvolution F 2 n) ∧
        (su2Bot (unitaryInvolution F 2 n)).map α.toMonoidHom =
          su2Bot (unitaryInvolution F 2 n) ∧
        (θ₂.comp (su3Chord (unitaryInvolution F 2 n))).comp α.symm.toMonoidHom = ψ := by
  let α : MulAut (SU (unitaryInvolution F 2 n) 2) := φe.trans ψe.symm
  have hαtop : (su2Top (unitaryInvolution F 2 n)).map α.toMonoidHom =
      su2Top (unitaryInvolution F 2 n) := by
    change (su2Top (unitaryInvolution F 2 n)).map
      (ψe.symm.toMonoidHom.comp φe.toMonoidHom) = _
    exact map_comp_symm_eq_of_map_eq (e₁ := φe) (e₂ := ψe)
      (S := su2Top (unitaryInvolution F 2 n)) (hφtop.trans hψtop.symm)
  have hαbot : (su2Bot (unitaryInvolution F 2 n)).map α.toMonoidHom =
      su2Bot (unitaryInvolution F 2 n) := by
    change (su2Bot (unitaryInvolution F 2 n)).map
      (ψe.symm.toMonoidHom.comp φe.toMonoidHom) = _
    exact map_comp_symm_eq_of_map_eq (e₁ := φe) (e₂ := ψe)
      (S := su2Bot (unitaryInvolution F 2 n)) (hφbot.trans hψbot.symm)
  have hφα : (θ₂.comp (su3Chord (unitaryInvolution F 2 n))).comp
      α.symm.toMonoidHom = ψ := by
    ext x
    change (θ₂.comp (su3Chord (unitaryInvolution F 2 n)))
      (α.symm x) = ψ x
    have hsymm : α.symm x = φe.symm (ψe x) := rfl
    rw [hsymm, ← hφval (φe.symm (ψe x))]
    simpa using hψval x
  exact ⟨α, hαtop, hαbot, hφα⟩

private theorem exists_block_beta (hFn : Nat.card F = (2 ^ n) ^ 2)
    {α : MulAut (SU (unitaryInvolution F 2 n) 2)}
    (hαtop : (su2Top (unitaryInvolution F 2 n)).map α.toMonoidHom =
      su2Top (unitaryInvolution F 2 n))
    (hαbot : (su2Bot (unitaryInvolution F 2 n)).map α.toMonoidHom =
      su2Bot (unitaryInvolution F 2 n)) :
    ∃ β : MulAut (SU (unitaryInvolution F 2 n) 3),
      β.toMonoidHom.comp (su3Chord (unitaryInvolution F 2 n)) =
          (su3Chord (unitaryInvolution F 2 n)).comp α.toMonoidHom ∧
        (su3Top (unitaryInvolution F 2 n)).map β.toMonoidHom =
          su3Top (unitaryInvolution F 2 n) := by
  obtain ⟨ε, τ, hε, hεσ, hτ, hα₁, hα₂⟩ :=
    su2_mulAut_aligned (F := F) (n := n) hFn α hαtop hαbot
  obtain ⟨β, hβ₁, hβ₂⟩ := exists_su3MulAut (F := F) (n := n) hFn hε hεσ τ hτ
  exact ⟨β, su3Chord_comp_of_aligned (F := F) (n := n) hFn hα₁ hα₂ hβ₁ hβ₂,
    (map_su3Top_of_aligned (F := F) (n := n) hε hεσ hτ hβ₁ hβ₂).1⟩

private theorem block_theta_basic
    {θ₂ : SU (unitaryInvolution F 2 n) 3 →* H}
    {β : MulAut (SU (unitaryInvolution F 2 n) 3)}
    {θ : SU (unitaryInvolution F 2 n) 3 →* H}
    (hθdef : θ = θ₂.comp β.symm.toMonoidHom)
    (hθ₂r : θ₂.range = residueGroup Δ P Q k)
    (hθ₂k : θ₂.ker ≤ Subgroup.center (SU (unitaryInvolution F 2 n) 3))
    (hθ₂odd : Odd (Nat.card θ₂.ker)) :
    θ.range = residueGroup Δ P Q k ∧
      θ.ker ≤ Subgroup.center (SU (unitaryInvolution F 2 n) 3) ∧
      Odd (Nat.card θ.ker) := by
  rw [hθdef]
  have hθr : (θ₂.comp β.symm.toMonoidHom).range = residueGroup Δ P Q k := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.2 β.symm.surjective,
      Subgroup.map_top, hθ₂r]
  have hker : (θ₂.comp β.symm.toMonoidHom).ker = (θ₂.ker).map β.toMonoidHom := by
    ext x
    constructor
    · intro hx
      refine ⟨β.symm x, ?_, by simp⟩
      show θ₂ (β.symm x) = 1
      simpa only [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom] using hx
    · rintro ⟨y, hy, rfl⟩
      show θ₂ (β.symm (β y)) = 1
      simpa [MulEquiv.coe_toMonoidHom] using hy
  have hθk : (θ₂.comp β.symm.toMonoidHom).ker ≤
      Subgroup.center (SU (unitaryInvolution F 2 n) 3) := by
    rw [hker]
    calc (θ₂.ker).map β.toMonoidHom ≤
          (Subgroup.center (SU (unitaryInvolution F 2 n) 3)).map β.toMonoidHom :=
          Subgroup.map_mono hθ₂k
      _ = Subgroup.center (SU (unitaryInvolution F 2 n) 3) := Subgroup.map_center_eq β
  have hθodd : Odd (Nat.card (θ₂.comp β.symm.toMonoidHom).ker) := by
    rw [hker, Subgroup.card_map_of_injective (f := β.toMonoidHom) β.injective]
    exact hθ₂odd
  exact ⟨hθr, hθk, hθodd⟩

private theorem block_theta_mem
    {θ₂ θ : SU (unitaryInvolution F 2 n) 3 →* H}
    {β : MulAut (SU (unitaryInvolution F 2 n) 3)}
    {α : MulAut (SU (unitaryInvolution F 2 n) 2)}
    {ψ : SU (unitaryInvolution F 2 n) 2 →* H}
    (hθdef : θ = θ₂.comp β.symm.toMonoidHom)
    (hβtop : (su3Top (unitaryInvolution F 2 n)).map β.toMonoidHom =
      su3Top (unitaryInvolution F 2 n))
    (hsquare : β.toMonoidHom.comp (su3Chord (unitaryInvolution F 2 n)) =
      (su3Chord (unitaryInvolution F 2 n)).comp α.toMonoidHom)
    (hφα : (θ₂.comp (su3Chord (unitaryInvolution F 2 n))).comp α.symm.toMonoidHom = ψ)
    (hθ₂mem : ∀ X : Subgroup H, X ∈ frameResidue Δ P Q k ↔
      ∃ g, X = (conjSub (su3Top (unitaryInvolution F 2 n)) g).map θ₂) :
    θ.comp (su3Chord (unitaryInvolution F 2 n)) = ψ ∧
      ∀ X : Subgroup H, X ∈ frameResidue Δ P Q k ↔
        ∃ g, X = (conjSub (su3Top (unitaryInvolution F 2 n)) g).map θ := by
  let σ := unitaryInvolution F 2 n
  let S3 : Subgroup (SU σ 3) := su3Top σ
  have hβsymm_top : S3.map β.symm.toMonoidHom = S3 :=
    (Subgroup.map_symm_eq_iff_map_eq S3).mpr hβtop
  have hmapθ : ∀ g : SU σ 3,
      (conjSub S3 g).map θ = (conjSub S3 (β.symm g)).map θ₂ := by
    intro g
    rw [hθdef, ← Subgroup.map_map,
      ← ModelRank.conjSub_map β.symm.toMonoidHom S3 g, hβsymm_top]
    simp
  have hβinvchord : β.symm.toMonoidHom.comp (su3Chord σ) =
      (su3Chord σ).comp α.symm.toMonoidHom := by
    apply MonoidHom.ext
    intro x
    have h := congrArg (fun f : SU σ 2 →* SU σ 3 => f (α.symm x)) hsquare
    have h' := congrArg β.symm h
    simpa using h'.symm
  have hθchord : θ.comp (su3Chord σ) = ψ := by
    rw [hθdef]
    change (θ₂.comp β.symm.toMonoidHom).comp (su3Chord σ) = ψ
    rw [MonoidHom.comp_assoc, hβinvchord, ← MonoidHom.comp_assoc]
    change (θ₂.comp (su3Chord σ)).comp α.symm.toMonoidHom = ψ
    exact hφα
  have hθmem : ∀ X : Subgroup H, X ∈ frameResidue Δ P Q k ↔
      ∃ g : SU σ 3, X = (conjSub S3 g).map θ := by
    intro X
    rw [hθ₂mem X]
    constructor
    · rintro ⟨g, rfl⟩
      refine ⟨β g, ?_⟩
      rw [hmapθ (β g)]
      simp [S3, σ]
    · rintro ⟨g, rfl⟩
      exact ⟨β.symm g, by simpa [S3, σ] using hmapθ g⟩
  exact ⟨hθchord, hθmem⟩

theorem IsMaxFrame.exists_su3_residue_block (h : TransvectionHyp H Δ) (hML : MeetsLines Δ)
    (hq : ∀ A ∈ Δ, 4 ≤ Nat.card A) (hF : IsMaxFrame Δ P Q)
    (hns : ¬ IsSmallFrame Δ P Q k) (hFn : Nat.card F = (2 ^ n) ^ 2)
    (hcard : ∀ A ∈ Δ, Nat.card A = 2 ^ n)
    (ψ : SU (unitaryInvolution F 2 n) 2 →* H)
    (ht : (su2Top (unitaryInvolution F 2 n)).map ψ = P k)
    (hb : (su2Bot (unitaryInvolution F 2 n)).map ψ = Q k) :
    ∃ θ : SU (unitaryInvolution F 2 n) 3 →* H,
      θ.range = residueGroup Δ P Q k ∧ θ.ker ≤ Subgroup.center _ ∧ Odd (Nat.card θ.ker) ∧
      θ.comp (su3Chord (unitaryInvolution F 2 n)) = ψ ∧
      ∀ X : Subgroup H, X ∈ frameResidue Δ P Q k ↔ ∃ g, X = (conjSub (su3Top _) g).map θ := by
  classical
  haveI : Finite H := h.finite
  obtain ⟨θ₂, hθ₂r, hθ₂k, hθ₂odd, hθ₂top, hθ₂bot, hθ₂mem⟩ :=
    IsMaxFrame.exists_su3_residue (Δ := Δ) (P := P) (Q := Q) (k := k)
      h hML hq hF hns hFn hcard
  obtain ⟨ψe, φe, hψval, hφval⟩ :=
    exists_SU2_equivs (F := F) (n := n) h.cls.root hF hq hcard hFn ψ ht hb hθ₂top hθ₂bot
  obtain ⟨hψtop, hψbot, hφtop, hφbot⟩ :=
    map_SU2_equivs (F := F) (n := n) ht hb hθ₂top hθ₂bot hψval hφval
  obtain ⟨α, hαtop, hαbot, hφα⟩ :=
    exists_block_alpha (F := F) (n := n) ψ hψtop hψbot hφtop hφbot hψval hφval
  obtain ⟨β, hsquare, hβtop⟩ :=
    exists_block_beta (F := F) (n := n) hFn hαtop hαbot
  let θ : SU (unitaryInvolution F 2 n) 3 →* H := θ₂.comp β.symm.toMonoidHom
  obtain ⟨hθr, hθk, hθodd⟩ :=
    block_theta_basic (F := F) (n := n) (k := k) (θ := θ) rfl hθ₂r hθ₂k hθ₂odd
  obtain ⟨hchord, hmem⟩ := block_theta_mem (F := F) (n := n) (k := k)
    (θ := θ) rfl hβtop hsquare hφα hθ₂mem
  exact ⟨θ, hθr, hθk, hθodd, hchord, hmem⟩

theorem IsMaxFrame.exists_su3_residue_last {m : ℕ} (he : Even m) (hm : 4 ≤ m)
    {P Q : Fin (m / 2) → Subgroup H} (h : TransvectionHyp H Δ) (hML : MeetsLines Δ)
    (hq : ∀ A ∈ Δ, 4 ≤ Nat.card A) (hF : IsMaxFrame Δ P Q)
    (hns : ¬ IsSmallFrame Δ P Q ⟨m / 2 - 1,
      Nat.sub_lt (Nat.div_pos (Nat.le_trans (Nat.le_add_right 2 2) hm) Nat.two_pos)
        Nat.zero_lt_one⟩)
    (hFn : Nat.card F = (2 ^ n) ^ 2) (hcard : ∀ A ∈ Δ, Nat.card A = 2 ^ n)
    (R : SURelations (m / 2) (unitaryInvolution F 2 n) H)
    (hR : R.HasFrameImages Δ P Q) :
    ∃ θ : SU (unitaryInvolution F 2 n) 3 →* H,
      θ.range = residueGroup Δ P Q ⟨m / 2 - 1,
        Nat.sub_lt (Nat.div_pos (Nat.le_trans (Nat.le_add_right 2 2) hm) Nat.two_pos)
          Nat.zero_lt_one⟩ ∧
        θ.ker ≤ Subgroup.center _ ∧ Odd (Nat.card θ.ker) ∧
        θ.comp (su3Chord (unitaryInvolution F 2 n)) = R.lastBlock hFn he hm ∧
        ∀ X : Subgroup H, X ∈ frameResidue Δ P Q ⟨m / 2 - 1,
          Nat.sub_lt (Nat.div_pos (Nat.le_trans (Nat.le_add_right 2 2) hm) Nat.two_pos)
            Nat.zero_lt_one⟩ ↔
          ∃ g, X = (conjSub (su3Top _) g).map θ := by
  have hmap := hR.map_lastBlock (F := F) (n := n) hFn he hm
  exact hF.exists_su3_residue_block (k := ⟨m / 2 - 1, by omega⟩)
    h hML hq hns hFn hcard (R.lastBlock hFn he hm) hmap.1 hmap.2


end AllCertificates

end CFSG.Timmesfeld.Transvection
