module

public import CFSG.Quasithin.H13.QRCPairLift

public section

namespace CFSG.Quasithin.H13.QRC

open Subgroup CFSG.ABGLocalTools CFSG.Quasithin.SteinbergBS CFSG.QuasithinUnique
  CFSG.QuasithinUnique.Setup

variable {H : Type} [Group H] [Finite H]

theorem bender_lift
    (hchar : IsCharacteristicP 2 H) (T : Sylow 2 H)
    (hTn : ¬ (T : Subgroup H).Normal) {M : Subgroup H} (hTM : (T : Subgroup H) ≤ M)
    (hMH : M < ⊤) (hmax : ∀ Y : Subgroup H, (T : Subgroup H) ≤ Y → Y < ⊤ → Y ≤ M)
    {V : Subgroup H} [IsElementaryAbelian 2 V] (hVT : V ≤ T)
    (hTV : (T : Subgroup H) ≤ normalizer (V : Set H)) (hVM : V ≤ inSubgroup (pCore 2) M)
    (hVQ : 4 ≤ (V ⊓ pCore 2 H).relIndex V) (hDK₀ : kerIn M ⊤ ≤ oddResidualPreimage H)
    {L : Subgroup (H ⧸ kerIn M ⊤)} {x : H ⧸ kerIn M ⊤} (hxL : x ∈ L)
    (hL : L = V.map (QuotientGroup.mk' (kerIn M ⊤)) ⊔
      conjugate (V.map (QuotientGroup.mk' (kerIn M ⊤))) x)
    (hLK : L ≤ (oddResidualPreimage H).map (QuotientGroup.mk' (kerIn M ⊤)))
    (hF : (∃ (f : ℕ) (k : Type) (_ : Field k), 2 ≤ f ∧ Nat.card k = 2 ^ f ∧
        Nonempty (L ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) k)) ∨
      ∃ (b : ℕ) (k : Type) (_ : Field k), 1 ≤ b ∧ Nat.card k = 2 ^ (2 * b + 1) ∧
        Nonempty (L ≃* CFSG.Blueprint.suzukiGroup b k))
    (hSF : IsSylowOf 2 ((T : Subgroup H).map (QuotientGroup.mk' (kerIn M ⊤)) ⊓ L) L)
    (hPFcore : kerIn (M.map (QuotientGroup.mk' (kerIn M ⊤)) ⊓ L) L = ⊥)
    (hFO : inSubgroup (pCore 2) L = ⊥)
    (hPFO : inSubgroup (pCore 2) (M.map (QuotientGroup.mk' (kerIn M ⊤)) ⊓ L) =
      (T : Subgroup H).map (QuotientGroup.mk' (kerIn M ⊤)) ⊓ L) :
    ∃ g : H, QuotientGroup.mk' (kerIn M ⊤) g = x ∧
      g ∈ V ⊔ conjugate V g ∧ V ⊔ conjugate V g ≤ oddResidualPreimage H ∧
      V < V ⊔ conjugate V g ∧
      (V ⊔ conjugate V g).map (QuotientGroup.mk' (kerIn M ⊤)) = L ∧
      L = V.map (QuotientGroup.mk' (kerIn M ⊤)) ⊔
        conjugate (V.map (QuotientGroup.mk' (kerIn M ⊤))) (QuotientGroup.mk' (kerIn M ⊤) g) ∧
      L.comap (QuotientGroup.mk' (kerIn M ⊤)) = kerIn M ⊤ ⊔ (V ⊔ conjugate V g) ∧
      ((V ⊔ conjugate V g).subgroupOf (pCore 2 H ⊔ (V ⊔ conjugate V g))).Normal ∧
      pCore 2 H ⊔ (V ⊔ conjugate V g) ≤ L.comap (QuotientGroup.mk' (kerIn M ⊤)) ∧
      ((pCore 2 H ⊔ (V ⊔ conjugate V g)).subgroupOf
        (L.comap (QuotientGroup.mk' (kerIn M ⊤)))).Normal ∧
      pCore 2 H ≤ normalizer ((V ⊔ conjugate V g : Subgroup H) : Set H) ∧
      ⁅kerIn M ⊤, V ⊔ conjugate V g⁆ ≤ pCore 2 H ∧
      IsSylowOf 2 ((T : Subgroup H) ⊓ (V ⊔ conjugate V g)) (V ⊔ conjugate V g) ∧
      (V ⊔ conjugate V g) ⊓ normalizer (V : Set H) ≤ M ⊓ (V ⊔ conjugate V g) ∧
      inSubgroup (pCore 2) (M ⊓ (V ⊔ conjugate V g)) =
        (T : Subgroup H) ⊓ (V ⊔ conjugate V g) ∧
      kerIn (M ⊓ (V ⊔ conjugate V g)) (V ⊔ conjugate V g) =
        inSubgroup (pCore 2) (V ⊔ conjugate V g) ∧
      kerIn (M ⊓ (V ⊔ conjugate V g)) (V ⊔ conjugate V g) = (V ⊔ conjugate V g) ⊓ kerIn M ⊤ ∧
      kerIn (M ⊓ (V ⊔ conjugate V g)) (V ⊔ conjugate V g) = (V ⊔ conjugate V g) ⊓ pCore 2 H ∧
      inSubgroup (pCore 2) (pCore 2 H ⊔ (V ⊔ conjugate V g)) = pCore 2 H ∧
      IsCharacteristicP 2 ↥(V ⊔ conjugate V g) ∧
      ∃ ψ : ↥(V ⊔ conjugate V g) →* L, Function.Surjective ψ ∧
        ψ.ker = (kerIn (M ⊓ (V ⊔ conjugate V g)) (V ⊔ conjugate V g)).subgroupOf
          (V ⊔ conjugate V g) ∧
        (∀ i : ↥(V ⊔ conjugate V g), (ψ i : H ⧸ kerIn M ⊤) = QuotientGroup.mk' (kerIn M ⊤) i) ∧
        ((M ⊓ (V ⊔ conjugate V g)).subgroupOf (V ⊔ conjugate V g)).map ψ =
          (M.map (QuotientGroup.mk' (kerIn M ⊤)) ⊓ L).subgroupOf L ∧
        (((T : Subgroup H) ⊓ (V ⊔ conjugate V g)).subgroupOf (V ⊔ conjugate V g)).map ψ =
          ((T : Subgroup H).map (QuotientGroup.mk' (kerIn M ⊤)) ⊓ L).subgroupOf L ∧
        (V.subgroupOf (V ⊔ conjugate V g)).map ψ =
          (V.map (QuotientGroup.mk' (kerIn M ⊤))).subgroupOf L := by
  classical
  have hπker : (QuotientGroup.mk' (kerIn M ⊤)).ker = kerIn M ⊤ := QuotientGroup.ker_mk' _
  have hVQ' : ¬ V ≤ pCore 2 H := by
    intro h
    rw [inf_eq_left.2 h, relIndex_self] at hVQ
    omega
  have hbot : IsElementaryAbelian 2 (⊥ : Subgroup (H ⧸ kerIn M ⊤)) :=
    { is_comm := ⟨fun _ _ => Subsingleton.elim _ _⟩
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun _ => Subsingleton.elim _ _ }
  have hEL : V.map (QuotientGroup.mk' (kerIn M ⊤)) ≤ L := hL ▸ le_sup_left
  have h9 := qrc_original_pair_lift_retains_central_second_factor hchar T hTn hTM hMH hmax hVT
    hTV hVM hVQ' (F := L) (A := ⊥) (fun _ _ _ ha => by rw [mem_bot.1 ha, mul_one, one_mul])
    (inf_bot_eq _) (x := x) (by rwa [sup_bot_eq]) (by rw [sup_bot_eq]; exact hL)
    (by
      rcases hF with ⟨f, k, _, hf, hk, he⟩ | ⟨b, k, _, hb, hk, he⟩
      · exact Or.inr (Or.inl ⟨f, k, inferInstance, hf, hk, he⟩)
      · exact Or.inr (Or.inr ⟨b, k, inferInstance, hb, hk, he⟩))
    hSF inf_le_right hPFcore hFO hPFO (by rw [sup_bot_eq, sup_bot_eq])
    (by rw [sup_bot_eq, sup_bot_eq])
  obtain ⟨g, hgI, hVI, hgx, h9⟩ := h9
  dsimp only at h9
  obtain ⟨hIF, hH₀, hIn, hQIH₀, hQIn, hQN, hcomm, hTIsyl, hID, -, hJcore, hJO, -, hQIO,
    hcharI, hO2MI, hNV, ψ, hψs, hψker, hψπ, hψM, hψT, hψV⟩ := h9
  rw [sup_bot_eq] at hIF hH₀ hQIH₀ hQIn
  have hJD : (V ⊔ conjugate V g) ⊓
      (⊥ : Subgroup (H ⧸ kerIn M ⊤)).comap (QuotientGroup.mk' (kerIn M ⊤)) =
        (V ⊔ conjugate V g) ⊓ kerIn M ⊤ := by
    rw [MonoidHom.comap_bot, hπker]
  rw [hJD] at hJcore hJO hQIO hψker
  have hψπ' : ∀ i : ↥(V ⊔ conjugate V g),
      (ψ i : H ⧸ kerIn M ⊤) = QuotientGroup.mk' (kerIn M ⊤) i := by
    intro i
    obtain ⟨a, ha, hai⟩ := hψπ i
    rw [hai, mem_bot.1 ha, mul_one]
  have hIK₀ : V ⊔ conjugate V g ≤ oddResidualPreimage H := by
    intro i hi
    have h1 : QuotientGroup.mk' (kerIn M ⊤) i ∈ L := hIF ▸ mem_map_of_mem _ hi
    obtain ⟨y, hy, hyi⟩ := hLK h1
    have h2 : y⁻¹ * i ∈ kerIn M ⊤ := by
      rw [← hπker, MonoidHom.mem_ker, map_mul, map_inv, hyi, inv_mul_cancel]
    have h3 := (oddResidualPreimage H).mul_mem hy (hDK₀ h2)
    rwa [mul_inv_cancel_left] at h3
  refine ⟨g, hgx, hgI, hIK₀, hVI, hIF, by rw [hgx]; exact hL, hH₀, hIn, hQIH₀, hQIn, hQN,
    hcomm, hTIsyl, hNV, hO2MI, ?_, hJcore.symm, hJcore.symm.trans hID, ?_, hcharI, ψ, hψs,
    by rw [hψker, hJcore], hψπ', hψM, hψT, ?_⟩
  · rw [← hJcore, hJO]
  · rw [hQIO, hID, sup_eq_left.2 inf_le_right]
  · rw [hψV, sup_bot_eq, inf_eq_left.2 hEL]

end CFSG.Quasithin.H13.QRC
