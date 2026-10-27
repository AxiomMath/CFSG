module

public import CFSG.Quasithin.Background.RonanE43Complement
public import CFSG.Quasithin.Background.RonanE43Sub

public section

open scoped commutatorElement

namespace CFSG.Quasithin.RonanE43

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.E3

section Helpers

theorem card_comap_of_surjective {G Γ : Type*} [Group G] [Group Γ] [Finite G] (π : G →* Γ)
    (hπ : Function.Surjective π) (X : Subgroup Γ) :
    Nat.card (X.comap π) = Nat.card π.ker * Nat.card X := by
  haveI : Finite Γ := Finite.of_surjective π hπ
  have h1 := Subgroup.card_mul_index (X.comap π)
  have h2 := Subgroup.card_mul_index X
  have h3 := Subgroup.card_ker_mul_card_of_surjective hπ
  rw [Subgroup.index_comap_of_surjective (H := X) (f := π) hπ] at h1
  have hpos : 0 < X.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have : Nat.card (X.comap π) * X.index = (Nat.card π.ker * Nat.card X) * X.index := by
    rw [h1, ← h3, ← h2]
    ring
  exact Nat.eq_of_mul_eq_mul_right hpos this

theorem card_map_of_injOn {G Γ : Type*} [Group G] [Group Γ] (π : G →* Γ) {C : Subgroup G}
    (hinj : ∀ x ∈ C, π x = 1 → x = 1) : Nat.card (C.map π) = Nat.card C := by
  have hinj' : Function.Injective (π.comp C.subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, Subgroup.eq_bot_iff_forall]
    intro x hx
    have h1 : π (x : G) = 1 := hx
    exact Subtype.ext (hinj x x.2 h1)
  have hrange : (π.comp C.subtype).range = C.map π := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  rw [← hrange]
  exact (Nat.card_congr (MonoidHom.ofInjective hinj').toEquiv).symm

theorem exists_A5Ext_of_injOn {G Γ : Type*} [Group G] [Group Γ] (π : G →* Γ) {Ah : Subgroup G}
    {Ab Vb : Subgroup Γ} (hAb : Ah.map π = Ab) (hinj : ∀ x ∈ Ah, π x = 1 → x = 1)
    (h : IsA5Ext Ab Vb) : ∃ Vh : Subgroup G, IsA5Ext Ah Vh := by
  obtain ⟨hVA, hV2, φ, hφs, hφk⟩ := h
  have hmem : ∀ x : ↥Ah, π (x : G) ∈ Ab := fun x => hAb ▸ Subgroup.mem_map_of_mem π x.2
  let ψ : ↥Ah →* ↥Ab := (π.comp Ah.subtype).codRestrict Ab hmem
  have hψinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have h1 : π (x : G) = 1 := congrArg Subtype.val hx
    exact Subtype.ext (hinj x x.2 h1)
  have hψs : Function.Surjective ψ := by
    intro a
    have : (a : Γ) ∈ Ah.map π := hAb ▸ a.2
    obtain ⟨x, hx, hxa⟩ := Subgroup.mem_map.mp this
    exact ⟨⟨x, hx⟩, Subtype.ext hxa⟩
  refine ⟨Ah ⊓ Vb.comap π, inf_le_left, ?_, φ.comp ψ, hφs.comp hψs, ?_⟩
  · let ϕ : ↥(Ah ⊓ Vb.comap π) →* ↥Vb :=
      (π.comp (Ah ⊓ Vb.comap π).subtype).codRestrict Vb (fun x => x.2.2)
    refine hV2.of_injective ϕ ?_
    rw [injective_iff_map_eq_one]
    intro x hx
    have h1 : π (x : G) = 1 := congrArg Subtype.val hx
    exact Subtype.ext (hinj x x.2.1 h1)
  · ext x
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ← MonoidHom.mem_ker, hφk,
      Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    show π (x : G) ∈ Vb ↔ (x : G) ∈ Ah ⊓ Vb.comap π
    exact ⟨fun h => ⟨x.2, h⟩, fun h => h.2⟩

theorem le_of_central_cover {G : Type*} [Group G] {L Q Z : Subgroup G} (hperf : L ≤ ⁅L, L⁆)
    (hQL : Q ≤ L) (hZL : Z ≤ L) (hZc : ∀ z ∈ Z, ∀ l ∈ L, z * l = l * z)
    (hLQ : ∀ l ∈ L, ∃ q ∈ Q, ∃ z ∈ Z, l = q * z) : L ≤ Q := by
  refine hperf.trans (Subgroup.commutator_le.mpr ?_)
  have hconj : ∀ z ∈ Z, ∀ x ∈ L, z * x * z⁻¹ = x := fun z hz x hx => by
    rw [hZc z hz x hx]
    group
  intro a ha b hb
  obtain ⟨q₁, hq₁, z₁, hz₁, rfl⟩ := hLQ a ha
  obtain ⟨q₂, hq₂, z₂, hz₂, rfl⟩ := hLQ b hb
  have hq₁L : q₁ ∈ L := hQL hq₁
  have hq₂L : q₂ ∈ L := hQL hq₂
  have step1 : ⁅q₁ * z₁, q₂ * z₂⁆ = ⁅q₁, q₂ * z₂⁆ := by
    rw [commutatorElement_def, commutatorElement_def]
    calc q₁ * z₁ * (q₂ * z₂) * (q₁ * z₁)⁻¹ * (q₂ * z₂)⁻¹
        = q₁ * (z₁ * (q₂ * z₂) * z₁⁻¹) * q₁⁻¹ * (q₂ * z₂)⁻¹ := by group
      _ = q₁ * (q₂ * z₂) * q₁⁻¹ * (q₂ * z₂)⁻¹ := by
        rw [hconj z₁ hz₁ (q₂ * z₂) (L.mul_mem hq₂L (hZL hz₂))]
  have step2 : ⁅q₁, q₂ * z₂⁆ = ⁅q₁, q₂⁆ := by
    rw [commutatorElement_def, commutatorElement_def]
    calc q₁ * (q₂ * z₂) * q₁⁻¹ * (q₂ * z₂)⁻¹
        = q₁ * q₂ * (z₂ * q₁⁻¹ * z₂⁻¹) * q₂⁻¹ := by group
      _ = q₁ * q₂ * q₁⁻¹ * q₂⁻¹ := by rw [hconj z₂ hz₂ q₁⁻¹ (L.inv_mem hq₁L)]
  rw [step1, step2, commutatorElement_def]
  exact Q.mul_mem (Q.mul_mem (Q.mul_mem hq₁ hq₂) (Q.inv_mem hq₁)) (Q.inv_mem hq₂)

end Helpers

section Lift

variable {G H : Type} [Group G] [Finite G] [Group H]

theorem goodFamily_of_lift3 (π : G →* H) (hπ : Function.Surjective π) {Z T L : Subgroup G}
    (hker : π.ker = Z) (hZ3 : Nat.card Z = 3) (hT : IsSylowIn 2 T ⊤) (hLT : L ⊔ T = ⊤)
    (hZL : Z ≤ L) (hZc : ∀ z ∈ Z, ∀ l ∈ L, z * l = l * z) (hperf : L ≤ ⁅L, L⁆)
    (h9 : ∀ x ∈ L, x ^ 3 ∈ Z → x ^ 3 = 1) {Ab Vb Pb : Subgroup H} (hA5 : IsA5Ext Ab Vb)
    (hAL : Ab ≤ L.map π) (hPL : Pb ≤ L.map π)
    (hAn : T.map π ≤ Subgroup.normalizer (Ab : Set H))
    (hPn : T.map π ≤ Subgroup.normalizer (Pb : Set H)) (hTP : T.map π ⊓ L.map π ≤ Pb)
    (hP3 : Nat.card Pb = 3 * Nat.card ↥(T.map π ⊓ L.map π))
    (hAc : ∃ m, Nat.card Ab = 3 * m ∧ ¬ 3 ∣ m) (hPc : ∃ m, Nat.card Pb = 3 * m ∧ ¬ 3 ∣ m)
    (hgen : L.map π ≤ (Ab ⊔ (T.map π ⊓ L.map π)) ⊔ Pb) : GoodFamily T 3 := by
  classical
  haveI : Finite H := Finite.of_surjective π hπ
  haveI hZn : Z.Normal := hker ▸ MonoidHom.normal_ker π
  have hT2 : IsPGroup 2 T := hT.isPGroup
  have hkerZ : ∀ x : G, π x = 1 ↔ x ∈ Z := fun x => by rw [← hker]; exact MonoidHom.mem_ker
  have hodd : Nat.Coprime (Nat.card π.ker) 2 := by rw [hker, hZ3]; norm_num
  have hTZ : T ≤ Subgroup.normalizer (Z : Set G) := by
    rw [Subgroup.normalizer_eq_top_iff.mpr hZn]
    exact le_top
  have key : ∀ X : Subgroup H, X ≤ L.map π →
      T.map π ≤ Subgroup.normalizer (X : Set H) → (∃ m, Nat.card X = 3 * m ∧ ¬ 3 ∣ m) →
      ∃ C : Subgroup G, C ≤ L ∧ C ⊓ Z = ⊥ ∧ C.map π = X ∧
        T ≤ Subgroup.normalizer (C : Set G) ∧
        ∀ x ∈ X.comap π, ∀ n : ℕ, x ^ 2 ^ n = 1 → x ∈ C := by
    intro X hXL hXn ⟨m, hm, hm3⟩
    have hKL : X.comap π ≤ L := by
      intro x hx
      obtain ⟨l, hl, hlx⟩ := Subgroup.mem_map.mp (hXL (Subgroup.mem_comap.mp hx))
      have hz : l⁻¹ * x ∈ Z := by
        rw [← hkerZ, map_mul, map_inv, hlx, inv_mul_cancel]
      have : x = l * (l⁻¹ * x) := by group
      rw [this]
      exact L.mul_mem hl (hZL hz)
    have hZK : Z ≤ X.comap π := by
      intro z hz
      rw [Subgroup.mem_comap, (hkerZ z).mpr hz]
      exact X.one_mem
    have hKcard : Nat.card (X.comap π) = 9 * m := by
      rw [card_comap_of_surjective π hπ, hker, hZ3, hm]
      ring
    have hTK : T ≤ Subgroup.normalizer ((X.comap π : Subgroup G) : Set G) := by
      intro t ht
      rw [Subgroup.mem_normalizer_iff]
      intro x
      have h1 := Subgroup.mem_normalizer_iff.mp (hXn (Subgroup.mem_map_of_mem π ht)) (π x)
      simp only [Subgroup.mem_comap, map_mul, map_inv]
      exact h1
    obtain ⟨C, hCK, hCZ, hCsup, hCn, hC2⟩ := exists_invariant_complement hZK hZ3
      (fun z hz k hk => hZc z hz k (hKL hk)) hTZ hTK hT2 hKcard hm3
      (fun x hx hx3 => h9 x (hKL hx) hx3)
    refine ⟨C, hCK.trans hKL, hCZ, ?_, hCn, fun x hx n hn => hC2 x hx n hn⟩
    apply le_antisymm
    · calc C.map π ≤ (X.comap π).map π := Subgroup.map_mono hCK
        _ ≤ X := Subgroup.map_comap_le π X
    · intro y hy
      obtain ⟨g, rfl⟩ := hπ y
      have hg : g ∈ C ⊔ Z := by rw [hCsup]; exact hy
      obtain ⟨c, hc, z, hz, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hg
      refine Subgroup.mem_map.mpr ⟨c, hc, ?_⟩
      rw [map_mul, (hkerZ z).mpr hz, mul_one]
  obtain ⟨Ca, hCaL, hCaZ, hCaπ, hCan, hCa2⟩ := key Ab hAL hAn hAc
  obtain ⟨Cp, hCpL, hCpZ, hCpπ, hCpn, hCp2⟩ := key Pb hPL hPn hPc
  have hinj : ∀ C : Subgroup G, C ⊓ Z = ⊥ → ∀ x ∈ C, π x = 1 → x = 1 :=
    fun C hCZ x hxC hx1 => by
      have : x ∈ C ⊓ Z := ⟨hxC, (hkerZ x).mp hx1⟩
      rw [hCZ] at this
      exact Subgroup.mem_bot.mp this
  obtain ⟨Vh, hA5h⟩ := exists_A5Ext_of_injOn π hCaπ (hinj Ca hCaZ) hA5
  have hCpcard : Nat.card Cp = Nat.card Pb := by
    rw [← hCpπ]
    exact (card_map_of_injOn π (hinj Cp hCpZ)).symm
  have hTL : (T ⊓ L).map π = T.map π ⊓ L.map π := by
    apply le_antisymm (Subgroup.map_inf_le _ _ _)
    rintro y ⟨hyT, hyL⟩
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp hyT
    obtain ⟨l, hl, hlt⟩ := Subgroup.mem_map.mp hyL
    have hz : l⁻¹ * t ∈ Z := by
      rw [← hkerZ, map_mul, map_inv, hlt, inv_mul_cancel]
    have htL : t ∈ L := by
      have : t = l * (l⁻¹ * t) := by group
      rw [this]
      exact L.mul_mem hl (hZL hz)
    exact Subgroup.mem_map_of_mem π ⟨ht, htL⟩
  have hTLcard : Nat.card ↥(T ⊓ L) = Nat.card ↥(T.map π ⊓ L.map π) := by
    rw [← hTL]
    exact (card_map_eq_of_odd_ker π hodd (hT2.to_le inf_le_left)).symm
  have hTLCp : T ⊓ L ≤ Cp := by
    rintro x ⟨hxT, hxL⟩
    obtain ⟨n, hn⟩ := hT2 ⟨x, hxT⟩
    exact hCp2 x (Subgroup.mem_comap.mpr
      (hTP ⟨Subgroup.mem_map_of_mem π hxT, Subgroup.mem_map_of_mem π hxL⟩)) n
      (by simpa using congrArg Subtype.val hn)
  have hgenL : L ≤ (Ca ⊔ T) ⊔ (Cp ⊔ T) := by
    set Q : Subgroup G := Ca ⊔ (T ⊓ L) ⊔ Cp with hQ
    have hQL : Q ≤ L := sup_le (sup_le hCaL inf_le_right) hCpL
    have hQmap : L.map π ≤ Q.map π := by
      rw [hQ, Subgroup.map_sup, Subgroup.map_sup, hCaπ, hTL, hCpπ]
      exact hgen
    have hLQ : ∀ l ∈ L, ∃ q ∈ Q, ∃ z ∈ Z, l = q * z := by
      intro l hl
      obtain ⟨q, hq, hqπ⟩ := hQmap (Subgroup.mem_map_of_mem π hl)
      refine ⟨q, hq, q⁻¹ * l, (hkerZ _).mp ?_, by group⟩
      rw [map_mul, map_inv, hqπ, inv_mul_cancel]
    have hLQ' : L ≤ Q := le_of_central_cover hperf hQL hZL hZc hLQ
    refine hLQ'.trans (sup_le (sup_le ?_ ?_) ?_)
    · exact le_sup_left.trans le_sup_left
    · exact inf_le_left.trans (le_sup_right.trans le_sup_left)
    · exact le_sup_left.trans le_sup_right
  exact goodFamily_of_subgroups hT hLT hA5h hCan hCpn hCpL hTLCp
    (by rw [hCpcard, hP3, hTLcard]) hgenL

end Lift

end CFSG.Quasithin.RonanE43
